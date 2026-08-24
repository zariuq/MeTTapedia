import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryParallelFrontier
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalCollapse

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

namespace ReflectiveContextSupport

/-- Free-variable renaming commutes with the post-order Quote/Drop
contraction because it does not alter constructor or list shape. -/
theorem renameFVars_finishNormalizeReflectiveApply
    (declaration : ReflectivePresentationDecl) (rename : String → String)
    (constructor : String) (arguments : List Pattern) :
    Pattern.renameFVars rename
        (finishNormalizeReflectiveApply declaration constructor arguments) =
      finishNormalizeReflectiveApply declaration constructor
        (arguments.map (Pattern.renameFVars rename)) := by
  by_cases quoted : constructor = declaration.quoteConstructor
  · subst constructor
    cases arguments with
    | nil => simp [finishNormalizeReflectiveApply, Pattern.renameFVars]
    | cons first rest =>
        cases rest with
        | nil =>
            cases first with
            | apply nestedConstructor nestedArguments =>
                cases nestedArguments with
                | nil =>
                    simp [finishNormalizeReflectiveApply,
                      Pattern.renameFVars]
                | cons name tail =>
                    cases tail with
                    | nil =>
                        by_cases dropped :
                            nestedConstructor = declaration.dropConstructor
                        · subst nestedConstructor
                          simp [finishNormalizeReflectiveApply,
                            Pattern.renameFVars]
                        · simp [finishNormalizeReflectiveApply,
                            Pattern.renameFVars, dropped]
                    | cons second tail =>
                        simp [finishNormalizeReflectiveApply,
                          Pattern.renameFVars]
            | bvar index =>
                simp [finishNormalizeReflectiveApply, Pattern.renameFVars]
            | fvar name =>
                simp [finishNormalizeReflectiveApply, Pattern.renameFVars]
            | lambda binder body =>
                simp [finishNormalizeReflectiveApply, Pattern.renameFVars]
            | multiLambda arity binders body =>
                simp [finishNormalizeReflectiveApply, Pattern.renameFVars]
            | subst body replacement =>
                simp [finishNormalizeReflectiveApply, Pattern.renameFVars]
            | collection collectionType elements rest =>
                simp [finishNormalizeReflectiveApply, Pattern.renameFVars]
        | cons second tail =>
            simp [finishNormalizeReflectiveApply, Pattern.renameFVars]
  · simp [finishNormalizeReflectiveApply, quoted, Pattern.renameFVars]

/-- An atom already restoring to a selected quotation can be compared with
another selected quotation at one depth: quotation resets the child depth, so
both quoted frames are independent of the ambient depth. -/
theorem restoresTogether_of_left_quote_of_substituteAt_eq
    (profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile)
    (support : ContextSupport.Support)
    (assignment : ContextSupport.Assignment)
    (quoteConstructor : String)
    (quoteIsQuote : isQuoteConstructor profile quoteConstructor = true)
    {left : Pattern} {leftArguments rightArguments : List Pattern}
    {depth : Nat}
    (leftQuote : RestoresTogether profile support assignment left
      (.apply quoteConstructor leftArguments))
    (equalAt : substituteAt profile support assignment depth left =
      substituteAt profile support assignment depth
        (.apply quoteConstructor rightArguments)) :
    RestoresTogether profile support assignment left
      (.apply quoteConstructor rightArguments) := by
  intro currentDepth
  calc
    substituteAt profile support assignment currentDepth left =
        substituteAt profile support assignment currentDepth
          (.apply quoteConstructor leftArguments) := leftQuote currentDepth
    _ = substituteAt profile support assignment depth
          (.apply quoteConstructor leftArguments) := by
        simp only [substituteAt, quoteIsQuote, if_true]
    _ = substituteAt profile support assignment depth left :=
      (leftQuote depth).symm
    _ = substituteAt profile support assignment depth
          (.apply quoteConstructor rightArguments) := equalAt
    _ = substituteAt profile support assignment currentDepth
          (.apply quoteConstructor rightArguments) := by
        simp only [substituteAt, quoteIsQuote, if_true]

/-- Symmetric companion of
`restoresTogether_of_left_quote_of_substituteAt_eq`. -/
theorem restoresTogether_of_right_quote_of_substituteAt_eq
    (profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile)
    (support : ContextSupport.Support)
    (assignment : ContextSupport.Assignment)
    (quoteConstructor : String)
    (quoteIsQuote : isQuoteConstructor profile quoteConstructor = true)
    {right : Pattern} {leftArguments rightArguments : List Pattern}
    {depth : Nat}
    (rightQuote : RestoresTogether profile support assignment right
      (.apply quoteConstructor rightArguments))
    (equalAt : substituteAt profile support assignment depth
        (.apply quoteConstructor leftArguments) =
      substituteAt profile support assignment depth right) :
    RestoresTogether profile support assignment
      (.apply quoteConstructor leftArguments) right := by
  exact (restoresTogether_of_left_quote_of_substituteAt_eq profile support
    assignment quoteConstructor quoteIsQuote rightQuote equalAt.symm).symm

/-- An atom restoring to one fixed selected quotation can be compared with
another selected quotation at one depth. Both quotation frames are independent
of the ambient restoration depth. -/
theorem restoresTogether_of_left_fixedQuote_of_substituteAt_eq
    (profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile)
    (support : ContextSupport.Support)
    (assignment : ContextSupport.Assignment)
    (quoteConstructor : String)
    (quoteIsQuote : isQuoteConstructor profile quoteConstructor = true)
    {left : Pattern} {leftArguments rightArguments : List Pattern}
    {depth : Nat}
    (leftQuote : ∀ currentDepth,
      substituteAt profile support assignment currentDepth left =
        .apply quoteConstructor leftArguments)
    (equalAt : substituteAt profile support assignment depth left =
      substituteAt profile support assignment depth
        (.apply quoteConstructor rightArguments)) :
    RestoresTogether profile support assignment left
      (.apply quoteConstructor rightArguments) := by
  intro currentDepth
  calc
    substituteAt profile support assignment currentDepth left =
        .apply quoteConstructor leftArguments := leftQuote currentDepth
    _ = substituteAt profile support assignment depth left :=
      (leftQuote depth).symm
    _ = substituteAt profile support assignment depth
          (.apply quoteConstructor rightArguments) := equalAt
    _ = substituteAt profile support assignment currentDepth
          (.apply quoteConstructor rightArguments) := by
        simp only [substituteAt, quoteIsQuote, if_true]

/-- Symmetric companion of
`restoresTogether_of_left_fixedQuote_of_substituteAt_eq`. -/
theorem restoresTogether_of_right_fixedQuote_of_substituteAt_eq
    (profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile)
    (support : ContextSupport.Support)
    (assignment : ContextSupport.Assignment)
    (quoteConstructor : String)
    (quoteIsQuote : isQuoteConstructor profile quoteConstructor = true)
    {right : Pattern} {leftArguments rightArguments : List Pattern}
    {depth : Nat}
    (rightQuote : ∀ currentDepth,
      substituteAt profile support assignment currentDepth right =
        .apply quoteConstructor rightArguments)
    (equalAt : substituteAt profile support assignment depth
        (.apply quoteConstructor leftArguments) =
      substituteAt profile support assignment depth right) :
    RestoresTogether profile support assignment
      (.apply quoteConstructor leftArguments) right := by
  exact (restoresTogether_of_left_fixedQuote_of_substituteAt_eq profile
    support assignment quoteConstructor quoteIsQuote rightQuote
      equalAt.symm).symm

/-- Substitution cannot manufacture an allowed non-quote application head
from a rigid semantic atom.  Hence an allowed head visible after restoration
was already the root constructor of the unrestored frame. -/
theorem exists_apply_eq_of_substituteAt_eq_apply_of_rigidAtoms
    (profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile)
    (support : ContextSupport.Support)
    (assignment : ContextSupport.Assignment)
    (allowed atomName : String → Prop)
    (quoteConstructor constructor : String)
    (constructorAllowed : allowed constructor)
    (constructorNeQuote : constructor ≠ quoteConstructor)
    (atomCases : ∀ name, atomName name →
      ((∀ depth,
        (∃ restoredName,
            substituteAt profile support assignment depth (.fvar name) =
              .fvar restoredName) ∨
          ∃ restoredConstructor arguments,
            ¬ allowed restoredConstructor ∧
            substituteAt profile support assignment depth (.fvar name) =
              .apply restoredConstructor arguments)) ∨
        ∃ arguments, ∀ depth,
          substituteAt profile support assignment depth (.fvar name) =
            .apply quoteConstructor arguments)
    {pattern : Pattern} {arguments : List Pattern} {depth : Nat}
    (supported : ConstructorsWithin allowed pattern)
    (atoms : ∀ name, name ∈ pattern.freeFvarNames → atomName name)
    (equal : substituteAt profile support assignment depth pattern =
      .apply constructor arguments) :
    ∃ rawArguments, pattern = .apply constructor rawArguments := by
  cases pattern with
  | bvar index =>
      simp only [substituteAt] at equal
      cases equal
  | fvar name =>
      have atom := atoms name (by simp [Pattern.freeFvarNames])
      rcases atomCases name atom with rigid | ⟨quotedArguments, quoted⟩
      · rcases rigid depth with ⟨restoredName, restored⟩ |
            ⟨restoredConstructor, restoredArguments, outside, restored⟩
        · rw [restored] at equal
          cases equal
        · rw [restored] at equal
          have constructorEq : restoredConstructor = constructor :=
            (Pattern.apply.inj equal).1
          exact (outside (constructorEq ▸ constructorAllowed)).elim
      · rw [quoted depth] at equal
        have quoteEq : quoteConstructor = constructor :=
          (Pattern.apply.inj equal).1
        exact (constructorNeQuote quoteEq.symm).elim
  | apply patternConstructor rawArguments =>
      simp only [substituteAt, Pattern.apply.injEq] at equal
      exact ⟨rawArguments,
        congrArg (fun head => Pattern.apply head rawArguments) equal.1⟩
  | lambda binder body =>
      simp only [substituteAt] at equal
      cases equal
  | multiLambda arity binders body =>
      simp only [substituteAt] at equal
      cases equal
  | subst body replacement =>
      simp only [substituteAt] at equal
      cases equal
  | collection collectionType elements rest =>
      simp only [substituteAt] at equal
      cases equal

/-- If one argument spine is the sole selected Drop and the two spines meet
at a common restoration apex, then the other spine has the same raw outer
shape.  The semantic-atom classification rules out manufacturing the allowed
Drop head during restoration. -/
theorem exists_right_drop_of_left_drop_of_argumentsApex
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl)
    (allowed atomName : String → Prop)
    (dropAllowed : allowed declaration.dropConstructor)
    (dropNeQuote : declaration.dropConstructor ≠
      declaration.quoteConstructor)
    (dropIsNotQuote : ReflectiveContextSupport.isQuoteConstructor
      source.costWholeReflectionProfile declaration.dropConstructor = false)
    (atomCases : ∀ name, atomName name →
      ((∀ depth,
        (∃ restoredName,
            substituteAt source.costWholeReflectionProfile cospan.commonSupport
                cospan.commonAssignment depth (.fvar name) =
              .fvar restoredName) ∨
          ∃ restoredConstructor arguments,
            ¬ allowed restoredConstructor ∧
            substituteAt source.costWholeReflectionProfile cospan.commonSupport
                cospan.commonAssignment depth (.fvar name) =
              .apply restoredConstructor arguments)) ∨
        ∃ arguments, ∀ depth,
          substituteAt source.costWholeReflectionProfile cospan.commonSupport
              cospan.commonAssignment depth (.fvar name) =
            .apply declaration.quoteConstructor arguments)
    {leftArguments rightArguments : List Pattern} {leftInner : Pattern}
    (argumentsApex : CostStaticAtomKeyCospan.CommonRestorationApexList source
      cospan declaration 0 leftArguments rightArguments)
    (rightSupported : ConstructorListWithin allowed rightArguments)
    (rightAtoms : ∀ name,
      name ∈ rightArguments.flatMap Pattern.freeFvarNames → atomName name)
    (leftShape : leftArguments =
      [.apply declaration.dropConstructor [leftInner]]) :
    ∃ rightInner,
      rightArguments = [.apply declaration.dropConstructor [rightInner]] := by
  subst leftArguments
  have restored :=
    CostStaticAtomKeyCospan.CommonRestorationApex.restoredList_eq argumentsApex
  have rightLength : rightArguments.length = 1 := by
    have lengths := congrArg List.length restored
    simpa using lengths.symm
  obtain ⟨rightHead, rfl⟩ := List.length_eq_one_iff.mp rightLength
  have headEqual :
      substituteAt source.costWholeReflectionProfile cospan.commonSupport
          cospan.commonAssignment 0 rightHead =
        .apply declaration.dropConstructor
          [substituteAt source.costWholeReflectionProfile cospan.commonSupport
            cospan.commonAssignment 0 leftInner] := by
    simpa only [List.map_cons, List.map_nil, List.cons.injEq,
      and_true, substituteAt, dropIsNotQuote, Bool.false_eq_true, if_false]
      using restored.symm
  obtain ⟨rawArguments, rightHeadShape⟩ :=
    exists_apply_eq_of_substituteAt_eq_apply_of_rigidAtoms
      source.costWholeReflectionProfile cospan.commonSupport
      cospan.commonAssignment allowed atomName declaration.quoteConstructor
      declaration.dropConstructor dropAllowed dropNeQuote atomCases
      rightSupported.1
      (fun name membership => rightAtoms name (by
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
        exact membership)) headEqual
  subst rightHead
  have headEqual' :
      Pattern.apply declaration.dropConstructor
          (rawArguments.map
            (substituteAt source.costWholeReflectionProfile
              cospan.commonSupport cospan.commonAssignment 0)) =
        Pattern.apply declaration.dropConstructor
          [substituteAt source.costWholeReflectionProfile cospan.commonSupport
            cospan.commonAssignment 0 leftInner] := by
    simpa only [substituteAt, dropIsNotQuote, Bool.false_eq_true, if_false]
      using headEqual
  have restoredRawArguments :
      rawArguments.map
          (substituteAt source.costWholeReflectionProfile cospan.commonSupport
            cospan.commonAssignment 0) =
        [substituteAt source.costWholeReflectionProfile cospan.commonSupport
          cospan.commonAssignment 0 leftInner] :=
    (Pattern.apply.inj headEqual').2
  have rawLength : rawArguments.length = 1 := by
    have lengths := congrArg List.length restoredRawArguments
    simpa using lengths
  obtain ⟨rightInner, rawShape⟩ := List.length_eq_one_iff.mp rawLength
  rw [rawShape]
  exact ⟨rightInner, rfl⟩

/-- A common argument apex synchronizes the only root-changing case of a
selected Quote: either both argument spines are the sole selected Drop, or
both Quote applications are retained. -/
theorem finishNormalizeReflectiveApply_quote_synchronized_of_argumentsApex
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl)
    (allowed atomName : String → Prop)
    (dropAllowed : allowed declaration.dropConstructor)
    (dropNeQuote : declaration.dropConstructor ≠
      declaration.quoteConstructor)
    (dropIsNotQuote : ReflectiveContextSupport.isQuoteConstructor
      source.costWholeReflectionProfile declaration.dropConstructor = false)
    (atomCases : ∀ name, atomName name →
      ((∀ depth,
        (∃ restoredName,
            substituteAt source.costWholeReflectionProfile cospan.commonSupport
                cospan.commonAssignment depth (.fvar name) =
              .fvar restoredName) ∨
          ∃ restoredConstructor arguments,
            ¬ allowed restoredConstructor ∧
            substituteAt source.costWholeReflectionProfile cospan.commonSupport
                cospan.commonAssignment depth (.fvar name) =
              .apply restoredConstructor arguments)) ∨
        ∃ arguments, ∀ depth,
          substituteAt source.costWholeReflectionProfile cospan.commonSupport
              cospan.commonAssignment depth (.fvar name) =
            .apply declaration.quoteConstructor arguments)
    {leftArguments rightArguments : List Pattern}
    (argumentsApex : CostStaticAtomKeyCospan.CommonRestorationApexList source
      cospan declaration 0 leftArguments rightArguments)
    (leftSupported : ConstructorListWithin allowed leftArguments)
    (rightSupported : ConstructorListWithin allowed rightArguments)
    (leftAtoms : ∀ name,
      name ∈ leftArguments.flatMap Pattern.freeFvarNames → atomName name)
    (rightAtoms : ∀ name,
      name ∈ rightArguments.flatMap Pattern.freeFvarNames → atomName name) :
    (∃ leftInner rightInner,
      leftArguments = [.apply declaration.dropConstructor [leftInner]] ∧
      rightArguments = [.apply declaration.dropConstructor [rightInner]]) ∨
      (Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
          declaration declaration.quoteConstructor leftArguments =
        .apply declaration.quoteConstructor leftArguments ∧
       Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
          declaration declaration.quoteConstructor rightArguments =
        .apply declaration.quoteConstructor rightArguments) := by
  rcases Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.finishNormalizeReflectiveApply_quote_cases
      declaration leftArguments
      with ⟨leftInner, leftShape, leftFinish⟩ | leftFinish
  · obtain ⟨rightInner, rightShape⟩ :=
      exists_right_drop_of_left_drop_of_argumentsApex cospan declaration
        allowed atomName dropAllowed dropNeQuote dropIsNotQuote atomCases
        argumentsApex rightSupported rightAtoms leftShape
    exact Or.inl ⟨leftInner, rightInner, leftShape, rightShape⟩
  · rcases Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.finishNormalizeReflectiveApply_quote_cases
        declaration rightArguments
        with ⟨rightInner, rightShape, rightFinish⟩ | rightFinish
    · have reversed :=
        CostStaticAtomKeyCospan.CommonRestorationApex.symmList argumentsApex
      obtain ⟨leftInner, leftShape⟩ :=
        exists_right_drop_of_left_drop_of_argumentsApex cospan declaration
          allowed atomName dropAllowed dropNeQuote dropIsNotQuote atomCases
          reversed leftSupported leftAtoms rightShape
      subst leftArguments
      have loop : leftInner = Pattern.apply declaration.quoteConstructor
          [Pattern.apply declaration.dropConstructor [leftInner]] := by
        exact (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.finishNormalizeReflectiveApply_quote_drop declaration
          leftInner).symm.trans leftFinish
      have smaller : sizeOf leftInner < sizeOf
          (Pattern.apply declaration.quoteConstructor
            [Pattern.apply declaration.dropConstructor [leftInner]]) := by
        simp_wf
        omega
      rw [← loop] at smaller
      exact (Nat.lt_irrefl _ smaller).elim
    · exact Or.inr ⟨leftFinish, rightFinish⟩

/-- Equality at one restoration depth is depth-uniform on a rigid frame whose
free-variable leaves are semantic atoms. The load-bearing separation is that
an atom restores either to a free variable, to an application outside the
rigid constructor fragment, or to one fixed selected quotation at every
depth. -/
theorem restoresTogether_of_substituteAt_eq_of_rigidAtoms
    (profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile)
    (support : ContextSupport.Support)
    (assignment : ContextSupport.Assignment)
    (allowed atomName : String → Prop)
    (quoteConstructor : String)
    (quoteIsQuote : isQuoteConstructor profile quoteConstructor = true)
    (atomCases : ∀ name, atomName name →
      ((∀ depth,
        (∃ restoredName,
            substituteAt profile support assignment depth (.fvar name) =
              .fvar restoredName) ∨
          ∃ constructor arguments,
            ¬ allowed constructor ∧
            substituteAt profile support assignment depth (.fvar name) =
              .apply constructor arguments)) ∨
        ∃ arguments, ∀ depth,
          substituteAt profile support assignment depth (.fvar name) =
            .apply quoteConstructor arguments)
    (atomPairs : ∀ {leftName rightName depth},
      atomName leftName → atomName rightName →
      substituteAt profile support assignment depth (.fvar leftName) =
        substituteAt profile support assignment depth (.fvar rightName) →
      RestoresTogether profile support assignment
        (.fvar leftName) (.fvar rightName)) :
    ∀ {left right depth},
      ConstructorsWithin allowed left →
      ConstructorsWithin allowed right →
      (∀ name, name ∈ left.freeFvarNames → atomName name) →
      (∀ name, name ∈ right.freeFvarNames → atomName name) →
      substituteAt profile support assignment depth left =
        substituteAt profile support assignment depth right →
      RestoresTogether profile support assignment left right := by
  intro left
  induction left using Pattern.inductionOn with
  | hbvar index =>
      intro right depth _leftSupported rightSupported leftAtoms rightAtoms equal
      cases right with
      | bvar rightIndex =>
          simp only [substituteAt, Pattern.bvar.injEq] at equal
          subst rightIndex
          exact RestoresTogether.refl profile support assignment (.bvar index)
      | fvar rightName =>
          have rightAtom := rightAtoms rightName (by simp [Pattern.freeFvarNames])
          rcases atomCases rightName rightAtom with rigid | ⟨arguments, quoted⟩
          · rcases rigid depth with ⟨restoredName, restored⟩ |
                ⟨constructor, arguments, _outside, restored⟩
            · rw [restored] at equal
              simp only [substituteAt] at equal
              cases equal
            · rw [restored] at equal
              simp only [substituteAt] at equal
              cases equal
          · rw [quoted depth] at equal
            simp only [substituteAt] at equal
            cases equal
      | apply constructor arguments =>
          simp only [substituteAt] at equal
          cases equal
      | lambda binder body =>
          simp only [substituteAt] at equal
          cases equal
      | multiLambda arity binders body =>
          simp only [substituteAt] at equal
          cases equal
      | subst body replacement =>
          simp only [substituteAt] at equal
          cases equal
      | collection collectionType elements rest =>
          simp only [substituteAt] at equal
          cases equal
  | hfvar leftName =>
      intro right depth _leftSupported rightSupported leftAtoms rightAtoms equal
      have leftAtom := leftAtoms leftName (by simp [Pattern.freeFvarNames])
      cases right with
      | bvar rightIndex =>
          rcases atomCases leftName leftAtom with rigid | ⟨arguments, quoted⟩
          · rcases rigid depth with ⟨restoredName, restored⟩ |
                ⟨constructor, arguments, _outside, restored⟩
            · rw [restored] at equal
              simp only [substituteAt] at equal
              cases equal
            · rw [restored] at equal
              simp only [substituteAt] at equal
              cases equal
          · rw [quoted depth] at equal
            simp only [substituteAt] at equal
            cases equal
      | fvar rightName =>
          have rightAtom := rightAtoms rightName (by simp [Pattern.freeFvarNames])
          exact atomPairs leftAtom rightAtom equal
      | apply rightConstructor rightArguments =>
          have rightAllowed : allowed rightConstructor := rightSupported.1
          rcases atomCases leftName leftAtom with rigid |
              ⟨atomArguments, quoted⟩
          · rcases rigid depth with ⟨restoredName, restored⟩ |
                ⟨atomConstructor, atomArguments, outside, restored⟩
            · rw [restored] at equal
              simp only [substituteAt] at equal
              cases equal
            · rw [restored] at equal
              simp only [substituteAt] at equal
              have constructorEq : atomConstructor = rightConstructor :=
                (Pattern.apply.inj equal).1
              exact (outside (constructorEq ▸ rightAllowed)).elim
          · have quotedEqual :
                .apply quoteConstructor atomArguments =
                  substituteAt profile support assignment depth
                    (.apply rightConstructor rightArguments) :=
              (quoted depth).symm.trans equal
            have constructorEq : quoteConstructor = rightConstructor := by
              have heads := Pattern.apply.inj (by
                simpa only [substituteAt] using quotedEqual)
              exact heads.1
            subst rightConstructor
            exact
              restoresTogether_of_left_fixedQuote_of_substituteAt_eq profile
                support assignment quoteConstructor quoteIsQuote quoted equal
      | lambda binder body =>
          rcases atomCases leftName leftAtom with rigid | ⟨arguments, quoted⟩
          · rcases rigid depth with ⟨restoredName, restored⟩ |
                ⟨constructor, arguments, _outside, restored⟩
            · rw [restored] at equal
              simp only [substituteAt] at equal
              cases equal
            · rw [restored] at equal
              simp only [substituteAt] at equal
              cases equal
          · rw [quoted depth] at equal
            simp only [substituteAt] at equal
            cases equal
      | multiLambda arity binders body =>
          rcases atomCases leftName leftAtom with rigid | ⟨arguments, quoted⟩
          · rcases rigid depth with ⟨restoredName, restored⟩ |
                ⟨constructor, arguments, _outside, restored⟩
            · rw [restored] at equal
              simp only [substituteAt] at equal
              cases equal
            · rw [restored] at equal
              simp only [substituteAt] at equal
              cases equal
          · rw [quoted depth] at equal
            simp only [substituteAt] at equal
            cases equal
      | subst body replacement =>
          rcases atomCases leftName leftAtom with rigid | ⟨arguments, quoted⟩
          · rcases rigid depth with ⟨restoredName, restored⟩ |
                ⟨constructor, arguments, _outside, restored⟩
            · rw [restored] at equal
              simp only [substituteAt] at equal
              cases equal
            · rw [restored] at equal
              simp only [substituteAt] at equal
              cases equal
          · rw [quoted depth] at equal
            simp only [substituteAt] at equal
            cases equal
      | collection collectionType elements rest =>
          rcases atomCases leftName leftAtom with rigid | ⟨arguments, quoted⟩
          · rcases rigid depth with ⟨restoredName, restored⟩ |
                ⟨constructor, arguments, _outside, restored⟩
            · rw [restored] at equal
              simp only [substituteAt] at equal
              cases equal
            · rw [restored] at equal
              simp only [substituteAt] at equal
              cases equal
          · rw [quoted depth] at equal
            simp only [substituteAt] at equal
            cases equal
  | happly leftConstructor leftArguments inductionHypothesis =>
      intro right depth leftSupported rightSupported leftAtoms rightAtoms equal
      cases right with
      | bvar rightIndex =>
          simp only [substituteAt] at equal
          cases equal
      | fvar rightName =>
          have rightAtom := rightAtoms rightName (by simp [Pattern.freeFvarNames])
          have leftAllowed : allowed leftConstructor := leftSupported.1
          rcases atomCases rightName rightAtom with rigid |
              ⟨atomArguments, quoted⟩
          · rcases rigid depth with ⟨restoredName, restored⟩ |
                ⟨atomConstructor, atomArguments, outside, restored⟩
            · rw [restored] at equal
              simp only [substituteAt] at equal
              cases equal
            · rw [restored] at equal
              simp only [substituteAt] at equal
              have constructorEq : leftConstructor = atomConstructor :=
                (Pattern.apply.inj equal).1
              exact (outside (constructorEq ▸ leftAllowed)).elim
          · have quotedEqual :
                substituteAt profile support assignment depth
                    (.apply leftConstructor leftArguments) =
                  .apply quoteConstructor atomArguments :=
              equal.trans (quoted depth)
            have constructorEq : leftConstructor = quoteConstructor := by
              have heads := Pattern.apply.inj (by
                simpa only [substituteAt] using quotedEqual)
              exact heads.1
            subst leftConstructor
            exact
              restoresTogether_of_right_fixedQuote_of_substituteAt_eq profile
                support assignment quoteConstructor quoteIsQuote quoted equal
      | apply rightConstructor rightArguments =>
          simp only [substituteAt, Pattern.apply.injEq] at equal
          have constructorEq : leftConstructor = rightConstructor := equal.1
          subst rightConstructor
          have argumentRestores : List.Forall₂
              (RestoresTogether profile support assignment)
              leftArguments rightArguments := by
            induction leftArguments generalizing rightArguments rightSupported
                rightAtoms with
            | nil =>
                cases rightArguments with
                | nil => exact .nil
                | cons rightHead rightTail => simp at equal
            | cons leftHead leftTail tailInduction =>
                cases rightArguments with
                | nil => simp at equal
                | cons rightHead rightTail =>
                    have argumentEq := equal.2
                    simp only [List.map_cons, List.cons.injEq] at argumentEq
                    have leftListSupported := leftSupported.2
                    have rightListSupported := rightSupported.2
                    have leftHeadSupported := leftListSupported.1
                    have leftTailSupported := leftListSupported.2
                    have rightHeadSupported := rightListSupported.1
                    have rightTailSupported := rightListSupported.2
                    have leftHeadAtoms : ∀ name,
                        name ∈ leftHead.freeFvarNames → atomName name := by
                      intro name membership
                      exact leftAtoms name (by
                        simp only [Pattern.freeFvarNames, List.mem_flatMap]
                        exact ⟨leftHead, List.mem_cons_self, membership⟩)
                    have rightHeadAtoms : ∀ name,
                        name ∈ rightHead.freeFvarNames → atomName name := by
                      intro name membership
                      exact rightAtoms name (by
                        simp only [Pattern.freeFvarNames, List.mem_flatMap]
                        exact ⟨rightHead, List.mem_cons_self, membership⟩)
                    have leftTailAtoms : ∀ pattern, pattern ∈ leftTail →
                        ∀ name, name ∈ pattern.freeFvarNames → atomName name := by
                      intro pattern patternMembership name nameMembership
                      exact leftAtoms name (by
                        simp only [Pattern.freeFvarNames, List.mem_flatMap]
                        exact ⟨pattern,
                          List.mem_cons_of_mem leftHead patternMembership,
                          nameMembership⟩)
                    have rightTailAtoms : ∀ pattern, pattern ∈ rightTail →
                        ∀ name, name ∈ pattern.freeFvarNames → atomName name := by
                      intro pattern patternMembership name nameMembership
                      exact rightAtoms name (by
                        simp only [Pattern.freeFvarNames, List.mem_flatMap]
                        exact ⟨pattern,
                          List.mem_cons_of_mem rightHead patternMembership,
                          nameMembership⟩)
                    have headRestores := inductionHypothesis leftHead
                      List.mem_cons_self (right := rightHead)
                      (depth := if isQuoteConstructor profile leftConstructor
                        then 0 else depth)
                      leftHeadSupported rightHeadSupported leftHeadAtoms
                      rightHeadAtoms argumentEq.1
                    have leftTailFrameSupported : ConstructorsWithin allowed
                        (.apply leftConstructor leftTail) :=
                      ⟨leftSupported.1, leftTailSupported⟩
                    have rightTailFrameSupported : ConstructorsWithin allowed
                        (.apply leftConstructor rightTail) :=
                      ⟨rightSupported.1, rightTailSupported⟩
                    have leftTailFrameAtoms : ∀ name,
                        name ∈ (Pattern.apply leftConstructor leftTail).freeFvarNames →
                          atomName name := by
                      intro name membership
                      simp only [Pattern.freeFvarNames, List.mem_flatMap] at membership
                      rcases membership with ⟨pattern, patternMembership,
                        nameMembership⟩
                      exact leftTailAtoms pattern patternMembership name
                        nameMembership
                    have rightTailFrameAtoms : ∀ name,
                        name ∈ (Pattern.apply leftConstructor rightTail).freeFvarNames →
                          atomName name := by
                      intro name membership
                      simp only [Pattern.freeFvarNames, List.mem_flatMap] at membership
                      rcases membership with ⟨pattern, patternMembership,
                        nameMembership⟩
                      exact rightTailAtoms pattern patternMembership name
                        nameMembership
                    have tailEqual :
                        leftConstructor = leftConstructor ∧
                          leftTail.map (substituteAt profile support assignment
                              (if isQuoteConstructor profile leftConstructor
                                then 0 else depth)) =
                            rightTail.map (substituteAt profile support assignment
                              (if isQuoteConstructor profile leftConstructor
                                then 0 else depth)) :=
                      ⟨rfl, argumentEq.2⟩
                    have tailRestores := tailInduction
                      (fun pattern membership => inductionHypothesis pattern
                        (List.mem_cons_of_mem leftHead membership))
                      (rightArguments := rightTail)
                      leftTailFrameSupported leftTailFrameAtoms
                      rightTailFrameSupported rightTailFrameAtoms tailEqual
                    exact .cons headRestores tailRestores
          exact RestoresTogether.apply argumentRestores
      | lambda binder body =>
          simp only [substituteAt] at equal
          cases equal
      | multiLambda arity binders body =>
          simp only [substituteAt] at equal
          cases equal
      | subst body replacement =>
          simp only [substituteAt] at equal
          cases equal
      | collection collectionType elements rest =>
          simp only [substituteAt] at equal
          cases equal
  | hlambda leftBinder leftBody inductionHypothesis =>
      intro right depth leftSupported rightSupported leftAtoms rightAtoms equal
      cases right with
      | bvar rightIndex => simp only [substituteAt] at equal; cases equal
      | fvar rightName =>
          have rightAtom := rightAtoms rightName (by simp [Pattern.freeFvarNames])
          rcases atomCases rightName rightAtom with rigid | ⟨arguments, quoted⟩
          · rcases rigid depth with ⟨restoredName, restored⟩ |
                ⟨constructor, arguments, _outside, restored⟩
            · rw [restored] at equal
              simp only [substituteAt] at equal
              cases equal
            · rw [restored] at equal
              simp only [substituteAt] at equal
              cases equal
          · rw [quoted depth] at equal
            simp only [substituteAt] at equal
            cases equal
      | apply constructor arguments =>
          simp only [substituteAt] at equal; cases equal
      | lambda rightBinder rightBody =>
          simp only [substituteAt, Pattern.lambda.injEq] at equal
          have binderEq : leftBinder = rightBinder := equal.1
          subst rightBinder
          apply RestoresTogether.lambda
          apply inductionHypothesis (right := rightBody) (depth := depth + 1)
            leftSupported rightSupported
          · intro name membership
            exact leftAtoms name (by simpa [Pattern.freeFvarNames] using membership)
          · intro name membership
            exact rightAtoms name (by simpa [Pattern.freeFvarNames] using membership)
          · exact equal.2
      | multiLambda arity binders body =>
          simp only [substituteAt] at equal; cases equal
      | subst body replacement =>
          simp only [substituteAt] at equal; cases equal
      | collection collectionType elements rest =>
          simp only [substituteAt] at equal; cases equal
  | hmultiLambda leftArity leftBinders leftBody inductionHypothesis =>
      intro right depth leftSupported rightSupported leftAtoms rightAtoms equal
      cases right with
      | bvar rightIndex => simp only [substituteAt] at equal; cases equal
      | fvar rightName =>
          have rightAtom := rightAtoms rightName (by simp [Pattern.freeFvarNames])
          rcases atomCases rightName rightAtom with rigid | ⟨arguments, quoted⟩
          · rcases rigid depth with ⟨restoredName, restored⟩ |
                ⟨constructor, arguments, _outside, restored⟩
            · rw [restored] at equal
              simp only [substituteAt] at equal
              cases equal
            · rw [restored] at equal
              simp only [substituteAt] at equal
              cases equal
          · rw [quoted depth] at equal
            simp only [substituteAt] at equal
            cases equal
      | apply constructor arguments =>
          simp only [substituteAt] at equal; cases equal
      | lambda binder body =>
          simp only [substituteAt] at equal; cases equal
      | multiLambda rightArity rightBinders rightBody =>
          simp only [substituteAt, Pattern.multiLambda.injEq] at equal
          have arityEq : leftArity = rightArity := equal.1
          have bindersEq : leftBinders = rightBinders := equal.2.1
          subst rightArity
          subst rightBinders
          apply RestoresTogether.multiLambda
          apply inductionHypothesis (right := rightBody)
            (depth := depth + leftArity) leftSupported rightSupported
          · intro name membership
            exact leftAtoms name (by simpa [Pattern.freeFvarNames] using membership)
          · intro name membership
            exact rightAtoms name (by simpa [Pattern.freeFvarNames] using membership)
          · exact equal.2.2
      | subst body replacement =>
          simp only [substituteAt] at equal; cases equal
      | collection collectionType elements rest =>
          simp only [substituteAt] at equal; cases equal
  | hsubst leftBody leftReplacement bodyInduction replacementInduction =>
      intro right depth leftSupported rightSupported leftAtoms rightAtoms equal
      cases right with
      | bvar rightIndex => simp only [substituteAt] at equal; cases equal
      | fvar rightName =>
          have rightAtom := rightAtoms rightName (by simp [Pattern.freeFvarNames])
          rcases atomCases rightName rightAtom with rigid | ⟨arguments, quoted⟩
          · rcases rigid depth with ⟨restoredName, restored⟩ |
                ⟨constructor, arguments, _outside, restored⟩
            · rw [restored] at equal
              simp only [substituteAt] at equal
              cases equal
            · rw [restored] at equal
              simp only [substituteAt] at equal
              cases equal
          · rw [quoted depth] at equal
            simp only [substituteAt] at equal
            cases equal
      | apply constructor arguments =>
          simp only [substituteAt] at equal; cases equal
      | lambda binder body =>
          simp only [substituteAt] at equal; cases equal
      | multiLambda arity binders body =>
          simp only [substituteAt] at equal; cases equal
      | subst rightBody rightReplacement =>
          simp only [substituteAt, Pattern.subst.injEq] at equal
          apply RestoresTogether.subst
          · apply bodyInduction (right := rightBody) (depth := depth + 1)
              leftSupported.1 rightSupported.1
            · intro name membership
              exact leftAtoms name (by
                simp [Pattern.freeFvarNames, membership])
            · intro name membership
              exact rightAtoms name (by
                simp [Pattern.freeFvarNames, membership])
            · exact equal.1
          · apply replacementInduction (right := rightReplacement)
              (depth := depth) leftSupported.2 rightSupported.2
            · intro name membership
              exact leftAtoms name (by
                simp [Pattern.freeFvarNames, membership])
            · intro name membership
              exact rightAtoms name (by
                simp [Pattern.freeFvarNames, membership])
            · exact equal.2
      | collection collectionType elements rest =>
          simp only [substituteAt] at equal; cases equal
  | hcollection leftType leftElements leftRest leftInduction =>
      intro right depth leftSupported rightSupported leftAtoms rightAtoms equal
      cases right with
      | bvar rightIndex => simp only [substituteAt] at equal; cases equal
      | fvar rightName =>
          have rightAtom := rightAtoms rightName (by simp [Pattern.freeFvarNames])
          rcases atomCases rightName rightAtom with rigid | ⟨arguments, quoted⟩
          · rcases rigid depth with ⟨restoredName, restored⟩ |
                ⟨constructor, arguments, _outside, restored⟩
            · rw [restored] at equal
              simp only [substituteAt] at equal
              cases equal
            · rw [restored] at equal
              simp only [substituteAt] at equal
              cases equal
          · rw [quoted depth] at equal
            simp only [substituteAt] at equal
            cases equal
      | apply constructor arguments =>
          simp only [substituteAt] at equal; cases equal
      | lambda binder body =>
          simp only [substituteAt] at equal; cases equal
      | multiLambda arity binders body =>
          simp only [substituteAt] at equal; cases equal
      | subst body replacement =>
          simp only [substituteAt] at equal; cases equal
      | collection rightType rightElements rightRest =>
          simp only [substituteAt, Pattern.collection.injEq] at equal
          have typeEq : leftType = rightType := equal.1
          have restEq : leftRest = rightRest := equal.2.2
          subst rightType
          subst rightRest
          have elementEq := equal.2.1
          have elementRestores : List.Forall₂
              (RestoresTogether profile support assignment)
              leftElements rightElements := by
            induction leftElements generalizing rightElements rightSupported
                rightAtoms with
            | nil =>
                cases rightElements with
                | nil => exact .nil
                | cons rightHead rightTail => simp at elementEq
            | cons leftHead leftTail tailInduction =>
                cases rightElements with
                | nil => simp at elementEq
                | cons rightHead rightTail =>
                    simp only [List.map_cons, List.cons.injEq] at elementEq
                    have leftHeadSupported := leftSupported.1
                    have leftTailSupported := leftSupported.2
                    have rightHeadSupported := rightSupported.1
                    have rightTailSupported := rightSupported.2
                    have leftHeadAtoms : ∀ name,
                        name ∈ leftHead.freeFvarNames → atomName name := by
                      intro name membership
                      exact leftAtoms name (by
                        simp only [Pattern.freeFvarNames, List.mem_append,
                          List.mem_flatMap]
                        exact Or.inl ⟨leftHead, List.mem_cons_self, membership⟩)
                    have rightHeadAtoms : ∀ name,
                        name ∈ rightHead.freeFvarNames → atomName name := by
                      intro name membership
                      exact rightAtoms name (by
                        simp only [Pattern.freeFvarNames, List.mem_append,
                          List.mem_flatMap]
                        exact Or.inl ⟨rightHead, List.mem_cons_self, membership⟩)
                    have leftTailAtoms : ∀ pattern, pattern ∈ leftTail →
                        ∀ name, name ∈ pattern.freeFvarNames → atomName name := by
                      intro pattern patternMembership name nameMembership
                      exact leftAtoms name (by
                        simp only [Pattern.freeFvarNames, List.mem_append,
                          List.mem_flatMap]
                        exact Or.inl ⟨pattern,
                          List.mem_cons_of_mem leftHead patternMembership,
                          nameMembership⟩)
                    have rightTailAtoms : ∀ pattern, pattern ∈ rightTail →
                        ∀ name, name ∈ pattern.freeFvarNames → atomName name := by
                      intro pattern patternMembership name nameMembership
                      exact rightAtoms name (by
                        simp only [Pattern.freeFvarNames, List.mem_append,
                          List.mem_flatMap]
                        exact Or.inl ⟨pattern,
                          List.mem_cons_of_mem rightHead patternMembership,
                          nameMembership⟩)
                    have headRestores := leftInduction leftHead
                      List.mem_cons_self (right := rightHead) (depth := depth)
                      leftHeadSupported
                      rightHeadSupported leftHeadAtoms rightHeadAtoms elementEq.1
                    have leftTailFrameSupported : ConstructorsWithin allowed
                        (.collection leftType leftTail leftRest) :=
                      leftTailSupported
                    have rightTailFrameSupported : ConstructorsWithin allowed
                        (.collection leftType rightTail leftRest) :=
                      rightTailSupported
                    have leftTailFrameAtoms : ∀ name,
                        name ∈ (Pattern.collection leftType leftTail leftRest).freeFvarNames →
                          atomName name := by
                      intro name membership
                      simp only [Pattern.freeFvarNames, List.mem_append,
                        List.mem_flatMap] at membership
                      rcases membership with membership | membership
                      · rcases membership with ⟨pattern, patternMembership,
                          nameMembership⟩
                        exact leftTailAtoms pattern patternMembership name
                          nameMembership
                      · exact leftAtoms name (by
                          simp only [Pattern.freeFvarNames, List.mem_append,
                            List.mem_flatMap]
                          exact Or.inr membership)
                    have rightTailFrameAtoms : ∀ name,
                        name ∈ (Pattern.collection leftType rightTail leftRest).freeFvarNames →
                          atomName name := by
                      intro name membership
                      simp only [Pattern.freeFvarNames, List.mem_append,
                        List.mem_flatMap] at membership
                      rcases membership with membership | membership
                      · rcases membership with ⟨pattern, patternMembership,
                          nameMembership⟩
                        exact rightTailAtoms pattern patternMembership name
                          nameMembership
                      · exact rightAtoms name (by
                          simp only [Pattern.freeFvarNames, List.mem_append,
                            List.mem_flatMap]
                          exact Or.inr membership)
                    have tailEqual :
                        leftType = leftType ∧
                          leftTail.map (substituteAt profile support assignment
                              depth) =
                            rightTail.map (substituteAt profile support assignment
                              depth) ∧
                          leftRest = leftRest :=
                      ⟨rfl, elementEq.2, rfl⟩
                    have tailRestores := tailInduction
                      (fun pattern membership => leftInduction pattern
                        (List.mem_cons_of_mem leftHead membership))
                      (rightElements := rightTail)
                      leftTailFrameSupported leftTailFrameAtoms
                      rightTailFrameSupported rightTailFrameAtoms tailEqual
                      elementEq.2
                    exact .cons headRestores tailRestores
          exact RestoresTogether.collection elementRestores

/-- The synchronized selected-Quote finish inherits depth-uniform
restoration from its argument apex. In the absorbing arm the rigid-frame
inversion descends through the two Drop shells; in the retained arm ordinary
Quote congruence resets both child depths to zero. -/
theorem restoresTogether_finishNormalizeReflectiveApply_quote_of_argumentsApex
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl)
    (allowed atomName : String → Prop)
    (quoteIsQuote : ReflectiveContextSupport.isQuoteConstructor
      source.costWholeReflectionProfile declaration.quoteConstructor = true)
    (dropAllowed : allowed declaration.dropConstructor)
    (dropNeQuote : declaration.dropConstructor ≠
      declaration.quoteConstructor)
    (dropIsNotQuote : ReflectiveContextSupport.isQuoteConstructor
      source.costWholeReflectionProfile declaration.dropConstructor = false)
    (atomCases : ∀ name, atomName name →
      ((∀ depth,
        (∃ restoredName,
            substituteAt source.costWholeReflectionProfile cospan.commonSupport
                cospan.commonAssignment depth (.fvar name) =
              .fvar restoredName) ∨
          ∃ restoredConstructor arguments,
            ¬ allowed restoredConstructor ∧
            substituteAt source.costWholeReflectionProfile cospan.commonSupport
                cospan.commonAssignment depth (.fvar name) =
              .apply restoredConstructor arguments)) ∨
        ∃ arguments, ∀ depth,
          substituteAt source.costWholeReflectionProfile cospan.commonSupport
              cospan.commonAssignment depth (.fvar name) =
            .apply declaration.quoteConstructor arguments)
    (atomPairs : ∀ {leftName rightName depth},
      atomName leftName → atomName rightName →
      substituteAt source.costWholeReflectionProfile cospan.commonSupport
          cospan.commonAssignment depth (.fvar leftName) =
        substituteAt source.costWholeReflectionProfile cospan.commonSupport
          cospan.commonAssignment depth (.fvar rightName) →
      RestoresTogether source.costWholeReflectionProfile cospan.commonSupport
        cospan.commonAssignment (.fvar leftName) (.fvar rightName))
    {leftArguments rightArguments : List Pattern}
    (argumentsApex : CostStaticAtomKeyCospan.CommonRestorationApexList source
      cospan declaration 0 leftArguments rightArguments)
    (leftSupported : ConstructorListWithin allowed leftArguments)
    (rightSupported : ConstructorListWithin allowed rightArguments)
    (leftAtoms : ∀ name,
      name ∈ leftArguments.flatMap Pattern.freeFvarNames → atomName name)
    (rightAtoms : ∀ name,
      name ∈ rightArguments.flatMap Pattern.freeFvarNames → atomName name) :
    RestoresTogether source.costWholeReflectionProfile cospan.commonSupport
      cospan.commonAssignment
      (Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
        declaration declaration.quoteConstructor leftArguments)
      (Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
        declaration declaration.quoteConstructor rightArguments) := by
  have synchronized :=
    finishNormalizeReflectiveApply_quote_synchronized_of_argumentsApex cospan
      declaration allowed atomName dropAllowed dropNeQuote dropIsNotQuote
      atomCases argumentsApex leftSupported rightSupported leftAtoms rightAtoms
  rcases synchronized with
      ⟨leftInner, rightInner, leftShape, rightShape⟩ |
        ⟨leftFinish, rightFinish⟩
  · subst leftArguments
    subst rightArguments
    have restored :=
      CostStaticAtomKeyCospan.CommonRestorationApex.restoredList_eq
        argumentsApex
    have restoredDropList :
        [Pattern.apply declaration.dropConstructor
            [substituteAt source.costWholeReflectionProfile cospan.commonSupport
              cospan.commonAssignment 0 leftInner]] =
          [Pattern.apply declaration.dropConstructor
            [substituteAt source.costWholeReflectionProfile cospan.commonSupport
              cospan.commonAssignment 0 rightInner]] := by
      simpa only [List.map_cons, List.map_nil, substituteAt, dropIsNotQuote,
        Bool.false_eq_true, if_false] using restored
    have restoredDrop :
        Pattern.apply declaration.dropConstructor
            [substituteAt source.costWholeReflectionProfile cospan.commonSupport
              cospan.commonAssignment 0 leftInner] =
          Pattern.apply declaration.dropConstructor
            [substituteAt source.costWholeReflectionProfile cospan.commonSupport
              cospan.commonAssignment 0 rightInner] :=
      (List.cons.inj restoredDropList).1
    have innerEqual :
        substituteAt source.costWholeReflectionProfile cospan.commonSupport
            cospan.commonAssignment 0 leftInner =
          substituteAt source.costWholeReflectionProfile cospan.commonSupport
            cospan.commonAssignment 0 rightInner := by
      exact (List.cons.inj (Pattern.apply.inj restoredDrop).2).1
    have innerRestores := restoresTogether_of_substituteAt_eq_of_rigidAtoms
      source.costWholeReflectionProfile cospan.commonSupport
      cospan.commonAssignment allowed atomName declaration.quoteConstructor
      quoteIsQuote atomCases atomPairs
      (left := leftInner) (right := rightInner) (depth := 0)
      leftSupported.1.2.1 rightSupported.1.2.1
      (fun name membership => leftAtoms name (by
        simpa [Pattern.freeFvarNames] using membership))
      (fun name membership => rightAtoms name (by
        simpa [Pattern.freeFvarNames] using membership)) innerEqual
    simpa only [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.finishNormalizeReflectiveApply_quote_drop]
      using innerRestores
  · intro depth
    rw [leftFinish, rightFinish]
    have quoted : CostStaticAtomKeyCospan.CommonRestorationApex source cospan
        declaration depth (.apply declaration.quoteConstructor leftArguments)
          (.apply declaration.quoteConstructor rightArguments) := by
      apply CostStaticAtomKeyCospan.CommonRestorationApex.apply
      simpa only [quoteIsQuote, if_true] using argumentsApex
    exact CostStaticAtomKeyCospan.CommonRestorationApex.restored_eq quoted

end ReflectiveContextSupport

end Mettapedia.GSLT.LanguageDef

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

@[simp]
theorem decodeCostBaseSortName_wrapped_eq_none :
    decodeCostBaseSortName costWrappedSortName = none := by
  cases decoded : decodeCostBaseSortName costWrappedSortName with
  | none => rfl
  | some sourceName =>
      have encoded : costWrappedSortName = costBaseSortTag ++ sourceName :=
        (decodeTaggedPayload_eq_some_iff costBaseSortTag costWrappedSortName
          sourceName).mp (by
            simpa only [decodeCostBaseSortName] using decoded)
      exact False.elim
        (costBaseSortName_ne_wrapped sourceName (by
          simpa only [costBaseSortName] using encoded.symm))

@[simp]
theorem decodeCostBaseSortName_apparatus_eq_none (kind : String) :
    decodeCostBaseSortName (costApparatusSortName kind) = none := by
  cases decoded : decodeCostBaseSortName (costApparatusSortName kind) with
  | none => rfl
  | some sourceName =>
      have encoded : costApparatusSortName kind =
          costBaseSortTag ++ sourceName :=
        (decodeTaggedPayload_eq_some_iff costBaseSortTag
          (costApparatusSortName kind) sourceName).mp (by
            simpa only [decodeCostBaseSortName] using decoded)
      exact False.elim
        (costBaseSortName_ne_apparatus sourceName kind (by
          simpa only [costBaseSortName] using encoded.symm))

@[simp]
theorem costApparatusSortName_ne_wrapped (kind : String) :
    costApparatusSortName kind ≠ costWrappedSortName :=
  (costWrappedSortName_ne_apparatus kind).symm

/-- A certified rho application boundary can only inhabit one of rho's two
authored result fibres. -/
theorem boundaryApplication_sourceType_name_or_proc
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {sourceBound targetBound sourceAvailable : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {_outer : OneHoleContext} {wireName : String}
    {arguments : List Pattern} {sourceType : TypeExpr}
    (constructor : rhoCIGSLT.DeclaredCostConstructor)
    (rendered : rhoCIGSLT.renderDeclaredCostConstructor constructor = wireName)
    (outsideCurrent : rhoCIGSLT.declaredCostConstructorRole constructor ≠
      .static color)
    (certified : CertifiedCostRegionBoundary rhoCIGSLT color targetFree
      sourceAvailable (mapTypeExpr (color.symbols rhoCIGSLT) sourceType)
      (.apply wireName arguments))
    (certifies : certifyCostRegionBoundary? rhoCIGSLT color targetFree
      sourceAvailable (mapTypeExpr (color.symbols rhoCIGSLT) sourceType)
      (.apply wireName arguments) = some certified) :
    sourceType = .base "Name" ∨ sourceType = .base "Proc" := by
  have interactingSort :
      rhoCIGSLT.theory.presentation.interactingSort.1.name = "Proc" := rfl
  have contentTyped : HasType rhoCIGSLT.costWholeLanguage targetFree
      sourceAvailable (.apply wireName arguments)
        (mapTypeExpr (color.symbols rhoCIGSLT) sourceType) := by
    simpa only [certified.content_eq, certified.targetSupport_eq,
      certified.targetType_eq] using certified.typed.contentTyped
  obtain ⟨rule, membership, label, _notBare, typeEq, _argumentsTyped⟩ :=
    hasType_apply_inversion contentTyped
  have coreMembership : rule ∈ rhoCIGSLT.costCoreLanguage.terms := by
    simpa only [rhoCIGSLT.costWholeLanguage_terms] using membership
  obtain ⟨typedConstructor, materializes⟩ :=
    rhoCIGSLT.exists_declaredCostConstructor_of_mem rule coreMembership
  have renderedRule :
      rhoCIGSLT.renderDeclaredCostConstructor typedConstructor = wireName := by
    calc
      rhoCIGSLT.renderDeclaredCostConstructor typedConstructor =
          (rhoCIGSLT.materializeDeclaredCostConstructor typedConstructor).label :=
        (rhoCIGSLT.materializeDeclaredCostConstructor_label
          typedConstructor).symm
      _ = rule.label := congrArg GrammarRule.label materializes
      _ = wireName := label.symm
  have constructorEq : typedConstructor = constructor :=
    rhoCIGSLT.renderDeclaredCostConstructor_injective
      (renderedRule.trans rendered.symm)
  subst typedConstructor
  have mappedTypeEq : mapTypeExpr (color.symbols rhoCIGSLT) sourceType =
      .base (rhoCIGSLT.materializeDeclaredCostConstructor constructor).category := by
    exact typeEq.trans
      (congrArg (fun materialized => TypeExpr.base materialized.category)
        materializes.symm)
  rcases constructor with ⟨constructor, declared⟩
  cases constructor with
  | base sourceConstructor =>
      rcases rho_rule_category_name_or_proc sourceConstructor.2 with
          category | category
      · left
        have decoded := congrArg
          (decodeCostStaticTypeExpr rhoCIGSLT color) mappedTypeEq
        rw [decodeCostStaticTypeExpr_mapTypeExpr] at decoded
        cases color <;>
          simp [CIGSLT.materializeDeclaredCostConstructor,
            costBaseConstructor, category, decodeCostStaticTypeExpr,
            decodeCostBaseSortName_encode, costBaseSortName_ne_wrapped,
            interactingSort] at decoded
        all_goals exact decoded
      · right
        have decoded := congrArg
          (decodeCostStaticTypeExpr rhoCIGSLT color) mappedTypeEq
        rw [decodeCostStaticTypeExpr_mapTypeExpr] at decoded
        cases color <;>
          simp [CIGSLT.materializeDeclaredCostConstructor,
            costBaseConstructor, category, decodeCostStaticTypeExpr,
            decodeCostBaseSortName_encode, costBaseSortName_ne_wrapped,
            interactingSort] at decoded
        all_goals exact decoded
  | wrapped sourceConstructor =>
      rcases rho_rule_category_name_or_proc sourceConstructor.2 with
          category | category
      · left
        have decoded := congrArg
          (decodeCostStaticTypeExpr rhoCIGSLT color) mappedTypeEq
        rw [decodeCostStaticTypeExpr_mapTypeExpr] at decoded
        cases color <;>
          simp [CIGSLT.materializeDeclaredCostConstructor,
            costWrappedConstructor, category, decodeCostStaticTypeExpr,
            decodeCostBaseSortName_encode, costBaseSortName_ne_wrapped,
            interactingSort] at decoded
        all_goals exact decoded
      · right
        have decoded := congrArg
          (decodeCostStaticTypeExpr rhoCIGSLT color) mappedTypeEq
        rw [decodeCostStaticTypeExpr_mapTypeExpr] at decoded
        cases color <;>
          simp [CIGSLT.materializeDeclaredCostConstructor,
            costWrappedConstructor, category, decodeCostStaticTypeExpr,
            interactingSort] at decoded
        all_goals exact decoded
  | apparatus kind =>
      have decoded := congrArg
        (decodeCostStaticTypeExpr rhoCIGSLT color) mappedTypeEq
      rw [decodeCostStaticTypeExpr_mapTypeExpr] at decoded
      right
      cases color <;> cases kind <;>
        simp [CIGSLT.materializeDeclaredCostConstructor,
          CostApparatusConstructor.grammarRule, decodeCostStaticTypeExpr,
          costSignatureSortName,
          costTokenStackSortName, costSignatureUnitConstructor,
          costSignatureProductConstructor, costSignedConstructor,
          costTokenStackEmptyConstructor, costTokenStackConsConstructor,
          costFundingConstructor, costContactConstructor,
          interactingSort] at decoded
      all_goals exact decoded

/-- A well-sorted object in rho's generated name fibre is a variable or one
of the two generated quotation forms. -/
theorem rho_costName_pattern_cases
    {targetFree : FreeTypeContext} {bound : List TypeExpr}
    {pattern : Pattern}
    (typed : HasType rhoCIGSLT.costWholeLanguage targetFree bound pattern
      (.base (costBaseSortName "Name")))
    (object : isObjectPattern pattern = true) :
    (∃ index, pattern = .bvar index) ∨
      (∃ name, pattern = .fvar name) ∨
      ∃ color : CostStaticColor, ∃ arguments,
        pattern = .apply
          ((color.symbols rhoCIGSLT).constructor "NQuote") arguments := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT .base
    rhoReflectivePresentation.toReflectivePresentationDecl
  have declarationMembership : declaration ∈
      rhoCIGSLT.costWholeReflectionProfile.presentations := by
    simpa [declaration] using
      CostHereditaryForeignBoundaryWitness.rhoDecl_mem_profile
        CostStaticColor.base
  have declarationNameSort : declaration.nameSort =
      costBaseSortName "Name" := by
    rfl
  generalize resultTypeEq : TypeExpr.base (costBaseSortName "Name") =
    resultType at typed
  cases typed with
  | bvar lookup => exact Or.inl ⟨_, rfl⟩
  | fvar lookup => exact Or.inr (Or.inl ⟨_, rfl⟩)
  | @constructor bound rule arguments membership notBare argumentsTyped =>
      have categoryEquality : rule.category = declaration.nameSort := by
        simpa only [declarationNameSort] using
          (TypeExpr.base.inj resultTypeEq.symm)
      have quoted :=
        (CostCanonicalLaws.rho_costReflectiveNameResultsQuoted declaration
          declarationMembership rule membership categoryEquality).1
      rcases rho_isQuoteConstructor_cases quoted with baseQuote | wrappedQuote
      · exact Or.inr (Or.inr ⟨.base, arguments, by
          simpa only [CostStaticColor.symbols_constructor,
            CostStaticColor.constructorTag, costBaseConstructorName] using
              congrArg (fun head => Pattern.apply head arguments) baseQuote⟩)
      · exact Or.inr (Or.inr ⟨.wrapped, arguments, by
          simpa only [CostStaticColor.symbols_constructor,
            CostStaticColor.constructorTag, costWrappedConstructorName] using
              congrArg (fun head => Pattern.apply head arguments)
                wrappedQuote⟩)
  | lambda bodyTyped => cases resultTypeEq
  | multiLambda bodyTyped => cases resultTypeEq
  | subst bodyTyped replacementTyped =>
      simp [isObjectPattern] at object
  | collection elementsTyped => cases resultTypeEq
  | @collectionConstructor bound rule parameterName collectionType elements
      rest elementType membership parameterShape elementsTyped =>
      have typedName : HasType rhoCIGSLT.costWholeLanguage targetFree bound
          (.collection collectionType elements rest)
          (.base declaration.nameSort) := by
        rw [declarationNameSort]
        rw [TypeExpr.base.inj resultTypeEq]
        exact
          (HasType.collectionConstructor membership parameterShape
            elementsTyped)
      exact (CostCanonicalLaws.rho_no_collection_at_reflectiveNameSort
        declaration declarationMembership typedName).elim

/-- A certified rho boundary in the authored name fibre is closed at the
quotation reset depth.  The boundary application cannot be a variable by
shape, while generated name applications are precisely coloured quotation
constructors. -/
theorem rho_boundaryNamePlan_pattern_isWellScopedAt_zero
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {sourceBound targetBound sourceAvailable : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {outer : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (sourceTypeName : sourceType = .base "Name")
    (boundaryClass : plan.rootClass.IsCertifiedBoundary) :
    pattern.isWellScopedAt 0 = true := by
  cases plan with
  | bvar => simp [CostStaticRegionPlan.rootClass,
      CostStaticPlanRootClass.IsCertifiedBoundary] at boundaryClass
  | fvar => simp [CostStaticRegionPlan.rootClass,
      CostStaticPlanRootClass.IsCertifiedBoundary] at boundaryClass
  | application =>
      simp [CostStaticRegionPlan.rootClass,
        CostStaticPlanRootClass.IsCertifiedBoundary] at boundaryClass
  | lambda => simp [CostStaticRegionPlan.rootClass,
      CostStaticPlanRootClass.IsCertifiedBoundary] at boundaryClass
  | multiLambda =>
      simp [CostStaticRegionPlan.rootClass,
        CostStaticPlanRootClass.IsCertifiedBoundary] at boundaryClass
  | collection =>
      simp [CostStaticRegionPlan.rootClass,
        CostStaticPlanRootClass.IsCertifiedBoundary] at boundaryClass
  | boundaryApplication constructor rendered outsideCurrent certified
      certifies =>
      rename_i wireName arguments
      have mappedName : mapTypeExpr (color.symbols rhoCIGSLT)
          (.base "Name") = .base (costBaseSortName "Name") := by
        cases color <;> rfl
      have typed : HasType rhoCIGSLT.costWholeLanguage targetFree
          sourceAvailable (.apply wireName arguments)
          (.base (costBaseSortName "Name")) := by
        have contentTyped := certified.typed.contentTyped
        rw [certified.content_eq, certified.targetSupport_eq,
          certified.targetType_eq, sourceTypeName, mappedName] at contentTyped
        exact contentTyped
      have contentObject : isObjectPattern (.apply wireName arguments) =
          true := by
        simpa only [certified.content_eq] using
          certified.typed.contentObjectPattern
      obtain ⟨rule, membership, label, _notBare, typeEq,
          argumentsTyped⟩ := hasType_apply_inversion typed
      let declaration := costStaticReflectivePresentationDecl rhoCIGSLT .base
        rhoReflectivePresentation.toReflectivePresentationDecl
      have declarationMembership : declaration ∈
          rhoCIGSLT.costWholeReflectionProfile.presentations := by
        simpa only [declaration] using
          CostHereditaryForeignBoundaryWitness.rhoDecl_mem_profile .base
      have categoryEquality : rule.category = declaration.nameSort := by
        have categoryEquality := (TypeExpr.base.inj typeEq).symm
        change rule.category = costBaseSortName "Name"
        exact categoryEquality
      have quoted : ReflectiveContextSupport.isQuoteConstructor
          rhoCIGSLT.costWholeReflectionProfile rule.label = true :=
        (CostCanonicalLaws.rho_costReflectiveNameResultsQuoted declaration
          declarationMembership rule membership categoryEquality).1
      have scopeSafe : ReflectiveWellSorted.ReflectiveScopeSafeAt
          rhoCIGSLT.costWholeReflectionProfile sourceAvailable.length
          (.apply rule.label arguments) := by
        simpa only [label, certified.content_eq,
          certified.targetSupport_eq] using
            certified.typed.contentReflectiveScopeSafe
      have argumentsAtZero :=
        WellSorted.isWellScopedListAt_zero_of_typed_quote
          rhoCIGSLT.costWholeLanguage_validate
          rhoCIGSLT.costWholeReflectionProfile_validate membership
          argumentsTyped quoted scopeSafe
      simpa only [Pattern.isWellScopedAt] using argumentsAtZero
  | boundaryCollection currentRejected oppositeChoice oppositeSelected
      certified certifies =>
      exact False.elim
        (rho_boundaryCollection_choices_absurd color targetFree targetBound
          _ _ _ oppositeSelected currentRejected)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
