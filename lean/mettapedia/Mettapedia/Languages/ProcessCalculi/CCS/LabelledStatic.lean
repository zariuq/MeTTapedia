import Mettapedia.Languages.ProcessCalculi.CCS.LabelledRenaming

/-!
# The static theory is a strong bisimulation

The labelled transitions of CCS with recursion respect its static theory: a process equivalent to another performs
the same actions, to equivalent targets.

The bag laws are read through the moves of a bag up to the order of its members (`BagMove`): one member moves, the
others staying, or two members synchronize. A transition of a bag is such a move (`bagMove_of_step`), and a move is a
transition up to the order of the target's members (`step_of_bagMove`), so a permutation of the members keeps the
moves (`BagMove.perm`).

Transitions keep typed object processes typed object processes (`LStep.typed`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.CCS.Recursive

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (liftIndex)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationEquiv DerivedInstance derivedInstance_equivalent
  equationEquiv_fill)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)
open Mettapedia.Languages.ProcessCalculi.CCS.Blocks (ccsBlock)

variable {definitions : List Definition}

/-! ## Typing -/

/-- **A transition keeps a typed object process a typed object process.** -/
theorem LStep.typed (admitted : admits definitions = true) {source : Pattern} {action : Action} {target : Pattern}
    (step : LStep definitions source action target) :
    ∀ {free : FreeTypeContext} {bound : List TypeExpr}, HasType ccsRecCalc free bound source (.base "Proc") →
      isObjectPattern source = true →
        HasType ccsRecCalc free bound target (.base "Proc") ∧ isObjectPattern target = true := by
  induction step with
  | @offer component guards offered k hk action continuation performs =>
      intro free bound typed object
      refine ⟨continuation_typed admitted typed offered hk performs, ?_⟩
      have guardObject := offers_guards_objects admitted object offered _ (List.getElem_mem hk)
      rcases guardAction_some performs with ⟨_, -, guardIs⟩ | ⟨_, -, guardIs⟩ | ⟨-, guardIs⟩ <;> rw [guardIs] at guardObject
      · exact Steps.object_of_prefix guardObject
      · exact Steps.object_of_prefix guardObject
      · exact Steps.object_of_tau guardObject
  | @par elements tail i hi action target inner recurse =>
      intro free bound typed object
      cases bag_tail_none object
      have members := members_of_bag (block := ccsBlock) typed
      have objects := bag_objects object
      obtain ⟨innerTyped, innerObject⟩ := recurse (members _ (List.getElem_mem hi)) (objects _ (List.getElem_mem hi))
      refine ⟨bag_typed (block := ccsBlock) ?_, isObject_bag.mpr ?_⟩
      · intro element member
        rcases List.mem_cons.mp member with rfl | inRest
        · exact innerTyped
        · exact members element (List.mem_of_mem_eraseIdx inRest)
      · intro element member
        rcases List.mem_cons.mp member with rfl | inRest
        · exact innerObject
        · exact objects element (List.mem_of_mem_eraseIdx inRest)
  | @sync elements tail i hi j hj name target target' first second firstRecurse secondRecurse =>
      intro free bound typed object
      cases bag_tail_none object
      have members := members_of_bag (block := ccsBlock) typed
      have objects := bag_objects object
      have firstMember := List.getElem_mem hi
      have secondMember := List.mem_of_mem_eraseIdx (List.getElem_mem hj)
      obtain ⟨firstTyped, firstObject⟩ := firstRecurse (members _ firstMember) (objects _ firstMember)
      obtain ⟨secondTyped, secondObject⟩ := secondRecurse (members _ secondMember) (objects _ secondMember)
      refine ⟨bag_typed (block := ccsBlock) ?_, isObject_bag.mpr ?_⟩
      · intro element member
        simp only [List.mem_cons] at member
        rcases member with rfl | rfl | inRest
        · exact firstTyped
        · exact secondTyped
        · exact members element (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx inRest))
      · intro element member
        simp only [List.mem_cons] at member
        rcases member with rfl | rfl | inRest
        · exact firstObject
        · exact secondObject
        · exact objects element (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx inRest))
  | @res binder source target action action' inner seen recurse =>
      intro free bound typed object
      cases restriction_binder (block := ccsBlock) typed
      have bodyObject : isObjectPattern source = true := by rwa [isObject_restriction] at object
      obtain ⟨innerTyped, innerObject⟩ := recurse (restriction_body (block := ccsBlock) typed) bodyObject
      exact ⟨ccsRecBlockLanguage.restrict_typed innerTyped, by rwa [isObject_restriction]⟩

/-! ## Moves of a bag -/

/-- **A move of a bag, up to the order of its members**: one member moves, the others staying; or two members
synchronize on an action and its co-action. -/
inductive BagMove (definitions : List Definition) : List Pattern → Action → List Pattern → Prop where
  | one {elements rest : List Pattern} {element target : Pattern} {action : Action}
      (perm : elements.Perm (element :: rest)) (step : LStep definitions element action target) :
      BagMove definitions elements action (target :: rest)
  | two {elements rest : List Pattern} {first second target target' name : Pattern}
      (perm : elements.Perm (first :: second :: rest)) (firstStep : LStep definitions first (.act name) target)
      (secondStep : LStep definitions second (.coact name) target') :
      BagMove definitions elements .tau (target :: target' :: rest)

/-- **A transition of a bag is a move of its members.** -/
theorem bagMove_of_step {elements : List Pattern} {tail : Option String} {action : Action} {target : Pattern}
    (step : LStep definitions (.collection .hashBag elements tail) action target) :
    ∃ result, BagMove definitions elements action result ∧ target = .collection .hashBag result none := by
  cases step with
  | offer offered => simp [offers] at offered
  | par i hi inner => exact ⟨_, .one (perm_getElem_eraseIdx elements i hi) inner, rfl⟩
  | sync i hi j hj first second =>
      exact ⟨_, .two ((perm_getElem_eraseIdx elements i hi).trans
        ((perm_getElem_eraseIdx (elements.eraseIdx i) j hj).cons _)) first second, rfl⟩

/-- **A move of the members is a transition of the bag**, up to the order of the target's members. -/
theorem step_of_bagMove {elements : List Pattern} {action : Action} {result : List Pattern}
    (move : BagMove definitions elements action result) (tail : Option String) :
    ∃ result', LStep definitions (.collection .hashBag elements tail) action (.collection .hashBag result' none) ∧
      result'.Perm result := by
  cases move with
  | @one rest element target _ perm step =>
      obtain ⟨i, hi, at', restPerm⟩ := index_of_perm_one perm
      exact ⟨_, .par i hi (at' ▸ step), restPerm.cons _⟩
  | @two rest first second target target' name perm firstStep secondStep =>
      obtain ⟨i, hi, j, hj, firstAt, secondAt, restPerm⟩ := indices_of_perm_two perm
      exact ⟨_, .sync i hi j hj (firstAt ▸ firstStep) (secondAt ▸ secondStep), (restPerm.cons _).cons _⟩

theorem BagMove.perm {elements elements' : List Pattern} {action : Action} {result : List Pattern}
    (move : BagMove definitions elements action result) (same : elements.Perm elements') :
    BagMove definitions elements' action result := by
  cases move with
  | one perm step => exact .one (same.symm.trans perm) step
  | two perm firstStep secondStep => exact .two (same.symm.trans perm) firstStep secondStep

/-- A move's result is a permutation of the members, the moving ones replaced. -/
theorem BagMove.result_cases {elements : List Pattern} {action : Action} {result : List Pattern}
    (move : BagMove definitions elements action result) :
    (∃ element rest target, elements.Perm (element :: rest) ∧ LStep definitions element action target ∧
        result = target :: rest) ∨
      ∃ first second rest target target' name, elements.Perm (first :: second :: rest) ∧
        LStep definitions first (.act name) target ∧ LStep definitions second (.coact name) target' ∧
        action = .tau ∧ result = target :: target' :: rest := by
  cases move with
  | one perm step => exact .inl ⟨_, _, _, perm, step, rfl⟩
  | two perm firstStep secondStep => exact .inr ⟨_, _, _, _, _, _, perm, firstStep, secondStep, rfl, rfl⟩

/-! ## What does not move -/

/-- Inaction has no transition. -/
theorem nil_no_step {action : Action} {target : Pattern} :
    ¬ LStep definitions (.apply "CNil" []) action target := by
  intro step
  generalize sourceIs : Pattern.apply "CNil" [] = source at step
  cases step with
  | offer offered => subst sourceIs; simp [offers] at offered
  | par => cases sourceIs
  | sync => cases sourceIs
  | res => simp at sourceIs

/-- A sum with no summand has no transition. -/
theorem emptySum_no_step {action : Action} {target : Pattern} :
    ¬ LStep definitions (.apply "CSum" [.collection .hashBag [] none]) action target := by
  intro step
  generalize sourceIs : Pattern.apply "CSum" [.collection .hashBag [] none] = source at step
  cases step with
  | offer offered k hk => subst sourceIs; simp [offers] at offered; subst offered; simp at hk
  | par => cases sourceIs
  | sync => cases sourceIs
  | res => simp at sourceIs

/-- A restriction of what has no transition has no transition. -/
theorem restriction_no_step {binder : Option String} {body : Pattern}
    (still : ∀ action target, ¬ LStep definitions body action target) {action : Action} {target : Pattern} :
    ¬ LStep definitions (.apply "CNu" [.lambda binder body]) action target := by
  intro step
  generalize sourceIs : Pattern.apply "CNu" [.lambda binder body] = source at step
  cases step with
  | offer offered => subst sourceIs; simp [offers] at offered
  | par => cases sourceIs
  | sync => cases sourceIs
  | res _ inner =>
      simp only [Pattern.apply.injEq, List.cons.injEq, Pattern.lambda.injEq, and_true, true_and] at sourceIs
      obtain ⟨-, rfl⟩ := sourceIs
      exact still _ _ inner

/-! ## Matching transitions -/

/-- **Transitions matched up to the static theory**: every transition of the first is matched by one of the second,
with the same action, to an equivalent target. -/
def Matched (definitions : List Definition) (first second : Pattern) : Prop :=
  ∀ ⦃action : Action⦄ ⦃target : Pattern⦄, LStep definitions first action target →
    ∃ target', LStep definitions second action target' ∧
      EquationEquiv (engineBasePremises RelationEnv.empty) ccsRecCalc target target'

theorem Matched.refl (process : Pattern) : Matched definitions process process :=
  fun _ target step => ⟨target, step, .refl _⟩

theorem Matched.trans {first second third : Pattern} (left : Matched definitions first second)
    (right : Matched definitions second third) : Matched definitions first third := by
  intro action target step
  obtain ⟨target', step', same⟩ := left step
  obtain ⟨target'', step'', same'⟩ := right step'
  exact ⟨target'', step'', .trans _ _ _ same same'⟩

/-- Processes with no transition match each other. -/
theorem matched_still {first second : Pattern} (still : ∀ action target, ¬ LStep definitions first action target) :
    Matched definitions first second :=
  fun _ _ step => absurd step (still _ _)

/-- A bag of members whose moves give equivalent results. -/
theorem bag_result_equivalent {free : FreeTypeContext} {bound : List TypeExpr} {result result' : List Pattern}
    (permutation : result.Perm result')
    (typed : HasType ccsRecCalc free bound (.collection .hashBag result none) (.base "Proc")) :
    EquationEquiv (engineBasePremises RelationEnv.empty) ccsRecCalc (.collection .hashBag result none)
      (.collection .hashBag result' none) :=
  derivedInstance_equivalent (DerivedInstance.bagPerm_of_sorted ⟨free, bound, typed⟩ permutation)

/-- **A permutation of a bag's members matches its transitions.** -/
theorem matched_bagPerm (admitted : admits definitions = true) {free : FreeTypeContext} {bound : List TypeExpr}
    {elements elements' : List Pattern} (permutation : elements.Perm elements')
    (typed : HasType ccsRecCalc free bound (.collection .hashBag elements none) (.base "Proc"))
    (object : isObjectPattern (.collection .hashBag elements none) = true) :
    Matched definitions (.collection .hashBag elements none) (.collection .hashBag elements' none) := by
  intro action target step
  obtain ⟨targetTyped, -⟩ := step.typed admitted typed object
  obtain ⟨result, move, rfl⟩ := bagMove_of_step step
  obtain ⟨result', step', resultPerm⟩ := step_of_bagMove (move.perm permutation) none
  exact ⟨_, step', bag_result_equivalent resultPerm.symm targetTyped⟩

/-- **A bag of one member matches the member.** -/
theorem matched_singleton (admitted : admits definitions = true) {free : FreeTypeContext} {bound : List TypeExpr}
    {element : Pattern} (typed : HasType ccsRecCalc free bound element (.base "Proc"))
    (object : isObjectPattern element = true) :
    Matched definitions (.collection .hashBag [element] none) element ∧
      Matched definitions element (.collection .hashBag [element] none) := by
  constructor
  · intro action target step
    obtain ⟨result, move, rfl⟩ := bagMove_of_step step
    rcases move.result_cases with ⟨member, rest, moved, perm, memberStep, rfl⟩ |
      ⟨first, second, rest, _, _, _, perm, _, _, _, rfl⟩
    · obtain ⟨rfl, rfl⟩ : member = element ∧ rest = [] := by
        simpa using List.perm_singleton.mp perm.symm
      obtain ⟨movedTyped, -⟩ := memberStep.typed admitted typed object
      exact ⟨moved, memberStep, derivedInstance_equivalent (ccsRecBlockLanguage.singleton movedTyped)⟩
    · have := perm.length_eq
      simp at this
  · intro action target step
    obtain ⟨movedTyped, -⟩ := step.typed admitted typed object
    refine ⟨.collection .hashBag [target] none, .par 0 (by simp) (by simpa using step), ?_⟩
    exact .symm _ _ (derivedInstance_equivalent (ccsRecBlockLanguage.singleton movedTyped))

/-! ## Inaction in a bag -/

theorem perm_cons_cons_of_ne {α : Type} [DecidableEq α] {list rest : List α} {kept moved : α}
    (perm : (kept :: list).Perm (moved :: rest)) (different : moved ≠ kept) :
    ∃ rest', rest.Perm (kept :: rest') ∧ list.Perm (moved :: rest') := by
  have keptMember : kept ∈ rest := by
    have inRight := perm.mem_iff.mp (List.mem_cons_self ..)
    rcases List.mem_cons.mp inRight with same | inRest
    · exact absurd same.symm different
    · exact inRest
  have restPerm := List.perm_cons_erase keptMember
  refine ⟨rest.erase kept, restPerm, ?_⟩
  have swapped : (kept :: list).Perm (kept :: moved :: rest.erase kept) :=
    perm.trans ((restPerm.cons moved).trans (List.Perm.swap kept moved _))
  exact swapped.cons_inv

/-- The members of a bag that a move leaves are members of the bag. -/
theorem members_of_perm {free : FreeTypeContext} {bound : List TypeExpr} {elements list : List Pattern}
    (members : Members ccsRecCalc ccsBlock free bound elements) (perm : elements.Perm list) :
    Members ccsRecCalc ccsBlock free bound list :=
  fun element member => members element (perm.mem_iff.mpr member)

theorem nil_typed {free : FreeTypeContext} {bound : List TypeExpr} :
    HasType ccsRecCalc free bound (.apply "CNil" []) (.base "Proc") :=
  ccsRecBlockLanguage.unit_typed

/-- **Inaction in a bag matches its absence.** -/
theorem matched_unitElim (admitted : admits definitions = true) {free : FreeTypeContext} {bound : List TypeExpr}
    {pre post : List Pattern}
    (typed : HasType ccsRecCalc free bound (.collection .hashBag (pre ++ .apply "CNil" [] :: post) none) (.base "Proc"))
    (object : isObjectPattern (.collection .hashBag (pre ++ .apply "CNil" [] :: post) none) = true) :
    Matched definitions (.collection .hashBag (pre ++ .apply "CNil" [] :: post) none)
        (.collection .hashBag (pre ++ post) none) ∧
      Matched definitions (.collection .hashBag (pre ++ post) none)
        (.collection .hashBag (pre ++ .apply "CNil" [] :: post) none) := by
  have members := members_of_bag (block := ccsBlock) typed
  have middle : (pre ++ .apply "CNil" [] :: post).Perm (.apply "CNil" [] :: (pre ++ post)) := List.perm_middle
  have dropped : ∀ {front rest : List Pattern},
      HasType ccsRecCalc free bound (.collection .hashBag (front ++ rest) none) (.base "Proc") →
      EquationEquiv (engineBasePremises RelationEnv.empty) ccsRecCalc
        (.collection .hashBag (front ++ .apply "CNil" [] :: rest) none) (.collection .hashBag (front ++ rest) none) := by
    intro front rest frontTyped
    have withNil : HasType ccsRecCalc free bound (.collection .hashBag (front ++ .apply "CNil" [] :: rest) none)
        (.base "Proc") := by
      apply bag_typed (block := ccsBlock) (rest := none)
      have frontMembers := members_of_bag (block := ccsBlock) frontTyped
      intro element member
      rcases List.mem_append.mp member with inFront | inRest
      · exact frontMembers element (List.mem_append_left _ inFront)
      · rcases List.mem_cons.mp inRest with rfl | inRest
        · exact nil_typed
        · exact frontMembers element (List.mem_append_right _ inRest)
    exact derivedInstance_equivalent (ccsRecBlockLanguage.unitElim withNil)
  constructor
  · intro action target step
    obtain ⟨targetTyped, -⟩ := step.typed admitted typed object
    obtain ⟨result, move, rfl⟩ := bagMove_of_step step
    rcases (move.perm middle).result_cases with ⟨member, rest, moved, perm, memberStep, rfl⟩ |
      ⟨first, second, rest, moved, moved', name, perm, firstStep, secondStep, rfl, rfl⟩
    · have notNil : member ≠ .apply "CNil" [] := fun same => nil_no_step (same ▸ memberStep)
      obtain ⟨rest', restPerm, listPerm⟩ := perm_cons_cons_of_ne perm notNil
      obtain ⟨result', step', resultPerm⟩ := step_of_bagMove (.one listPerm memberStep) none
      refine ⟨_, step', ?_⟩
      have reordered := bag_result_equivalent (restPerm.cons moved) targetTyped
      have reorderedTyped : HasType ccsRecCalc free bound
          (.collection .hashBag (moved :: .apply "CNil" [] :: rest') none) (.base "Proc") :=
        bag_typed (block := ccsBlock) (members_of_perm (members_of_bag (block := ccsBlock) targetTyped)
          (restPerm.cons moved))
      have withoutNil := dropped (front := [moved]) (rest := rest') (by
        apply bag_typed (block := ccsBlock) (rest := none)
        intro element member
        exact members_of_bag (block := ccsBlock) reorderedTyped element (by
          simp only [List.singleton_append, List.mem_cons] at member ⊢
          tauto))
      simp only [List.singleton_append] at withoutNil
      have resultTyped : HasType ccsRecCalc free bound (.collection .hashBag (moved :: rest') none) (.base "Proc") := by
        apply bag_typed (block := ccsBlock) (rest := none)
        intro element member
        exact members_of_bag (block := ccsBlock) reorderedTyped element (by
          simp only [List.mem_cons] at member ⊢
          tauto)
      exact .trans _ _ _ reordered (.trans _ _ _ withoutNil (bag_result_equivalent resultPerm.symm resultTyped))
    · have firstNotNil : first ≠ .apply "CNil" [] := fun same => nil_no_step (same ▸ firstStep)
      have secondNotNil : second ≠ .apply "CNil" [] := fun same => nil_no_step (same ▸ secondStep)
      obtain ⟨rest₁, restPerm₁, listPerm₁⟩ := perm_cons_cons_of_ne perm firstNotNil
      obtain ⟨rest₂, restPerm₂, listPerm₂⟩ := perm_cons_cons_of_ne restPerm₁.symm secondNotNil
      have listPerm : (pre ++ post).Perm (first :: second :: rest₂) := listPerm₁.trans (listPerm₂.cons first)
      obtain ⟨result', step', resultPerm⟩ := step_of_bagMove (.two listPerm firstStep secondStep) none
      refine ⟨_, step', ?_⟩
      have restIs : rest.Perm (.apply "CNil" [] :: rest₂) := restPerm₂
      have reordered := bag_result_equivalent ((restIs.cons moved').cons moved) targetTyped
      have reorderedTyped : HasType ccsRecCalc free bound
          (.collection .hashBag (moved :: moved' :: .apply "CNil" [] :: rest₂) none) (.base "Proc") :=
        bag_typed (block := ccsBlock) (members_of_perm (members_of_bag (block := ccsBlock) targetTyped)
          ((restIs.cons moved').cons moved))
      have withoutNil := dropped (front := [moved, moved']) (rest := rest₂) (by
        apply bag_typed (block := ccsBlock) (rest := none)
        intro element member
        exact members_of_bag (block := ccsBlock) reorderedTyped element (by
          simp only [List.cons_append, List.nil_append, List.mem_cons] at member ⊢
          tauto))
      simp only [List.cons_append, List.nil_append] at withoutNil
      have resultTyped : HasType ccsRecCalc free bound (.collection .hashBag (moved :: moved' :: rest₂) none)
          (.base "Proc") := by
        apply bag_typed (block := ccsBlock) (rest := none)
        intro element member
        exact members_of_bag (block := ccsBlock) reorderedTyped element (by
          simp only [List.mem_cons] at member ⊢
          tauto)
      exact .trans _ _ _ reordered (.trans _ _ _ withoutNil (bag_result_equivalent resultPerm.symm resultTyped))
  · have shorterTyped : HasType ccsRecCalc free bound (.collection .hashBag (pre ++ post) none) (.base "Proc") := by
      apply bag_typed (block := ccsBlock) (rest := none)
      intro element member
      exact members element (by
        rcases List.mem_append.mp member with inPre | inPost
        · exact List.mem_append_left _ inPre
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ inPost))
    have shorterObject : isObjectPattern (.collection .hashBag (pre ++ post) none) = true := by
      have objects := bag_objects object
      exact isObject_bag.mpr fun element member => objects element (by
        rcases List.mem_append.mp member with inPre | inPost
        · exact List.mem_append_left _ inPre
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ inPost))
    intro action target step
    obtain ⟨targetTyped, -⟩ := step.typed admitted shorterTyped shorterObject
    obtain ⟨result, move, rfl⟩ := bagMove_of_step step
    rcases move.result_cases with ⟨member, rest, moved, perm, memberStep, rfl⟩ |
      ⟨first, second, rest, moved, moved', name, perm, firstStep, secondStep, rfl, rfl⟩
    · have withNil : (pre ++ .apply "CNil" [] :: post).Perm (member :: .apply "CNil" [] :: rest) :=
        middle.trans ((perm.cons _).trans (List.Perm.swap _ _ _))
      obtain ⟨result', step', resultPerm⟩ := step_of_bagMove (.one withNil memberStep) none
      refine ⟨_, step', ?_⟩
      have withoutNil := dropped (front := [moved]) (rest := rest) (by simpa using targetTyped)
      simp only [List.singleton_append] at withoutNil
      have resultTyped := (step'.typed admitted typed object).1
      exact .trans _ _ _ (.symm _ _ withoutNil) (bag_result_equivalent resultPerm.symm (by
        apply bag_typed (block := ccsBlock) (rest := none)
        intro element member
        exact members_of_bag (block := ccsBlock) resultTyped element (resultPerm.mem_iff.mpr member)))
    · have withNil : (pre ++ .apply "CNil" [] :: post).Perm (first :: second :: .apply "CNil" [] :: rest) :=
        middle.trans ((perm.cons _).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons _)))
      obtain ⟨result', step', resultPerm⟩ := step_of_bagMove (.two withNil firstStep secondStep) none
      refine ⟨_, step', ?_⟩
      have withoutNil := dropped (front := [moved, moved']) (rest := rest) (by simpa using targetTyped)
      simp only [List.cons_append, List.nil_append] at withoutNil
      have resultTyped := (step'.typed admitted typed object).1
      exact .trans _ _ _ (.symm _ _ withoutNil) (bag_result_equivalent resultPerm.symm (by
        apply bag_typed (block := ccsBlock) (rest := none)
        intro element member
        exact members_of_bag (block := ccsBlock) resultTyped element (resultPerm.mem_iff.mpr member)))

/-! ## A bag inside a bag -/

/-- A move of some members is a move of more, the others staying. -/
theorem BagMove.extend {elements result : List Pattern} {action : Action}
    (move : BagMove definitions elements action result) (extra : List Pattern) :
    BagMove definitions (elements ++ extra) action (result ++ extra) := by
  cases move with
  | one perm step => exact .one (perm.append_right extra) step
  | two perm firstStep secondStep => exact .two (perm.append_right extra) firstStep secondStep

theorem typed_of_members {free : FreeTypeContext} {bound : List TypeExpr} {elements list : List Pattern}
    (typed : HasType ccsRecCalc free bound (.collection .hashBag elements none) (.base "Proc"))
    (within : ∀ element ∈ list, element ∈ elements) :
    HasType ccsRecCalc free bound (.collection .hashBag list none) (.base "Proc") :=
  bag_typed (block := ccsBlock) (rest := none) fun element member =>
    members_of_bag (block := ccsBlock) typed element (within element member)

/-- Close a permutation of lists by comparing them as multisets. -/
theorem perm_of_multiset {α : Type} {list list' : List α} (same : (list : Multiset α) = list') : list.Perm list' :=
  Multiset.coe_eq_coe.mp same

/-- A permutation of lists built from the same members, closed as an equation of multisets. -/
macro "perm_ac" : tactic =>
  `(tactic| (apply perm_of_multiset <;> simp only [← Multiset.cons_coe, ← Multiset.coe_add, ← Multiset.singleton_add,
    Multiset.cons_add, List.cons_append, List.append_assoc] <;> ac_rfl))

/-- **A bag inside a bag matches its members spliced in.** -/
theorem matched_flatten (admitted : admits definitions = true) {free : FreeTypeContext} {bound : List TypeExpr}
    {inner others : List Pattern}
    (typed : HasType ccsRecCalc free bound (.collection .hashBag (.collection .hashBag inner none :: others) none)
      (.base "Proc"))
    (object : isObjectPattern (.collection .hashBag (.collection .hashBag inner none :: others) none) = true) :
    Matched definitions (.collection .hashBag (.collection .hashBag inner none :: others) none)
        (.collection .hashBag (inner ++ others) none) ∧
      Matched definitions (.collection .hashBag (inner ++ others) none)
        (.collection .hashBag (.collection .hashBag inner none :: others) none) := by
  have members := members_of_bag (block := ccsBlock) typed
  have nestedTyped := members _ List.mem_cons_self
  have innerMembers := members_of_bag (block := ccsBlock) nestedTyped
  have othersMembers : Members ccsRecCalc ccsBlock free bound others :=
    fun element member => members element (List.mem_cons_of_mem _ member)
  have flatTyped : HasType ccsRecCalc free bound (.collection .hashBag (inner ++ others) none) (.base "Proc") :=
    bag_typed (block := ccsBlock) (rest := none) fun element member =>
      (List.mem_append.mp member).elim (innerMembers element) (othersMembers element)
  have objects := bag_objects object
  have innerObjects := bag_objects (objects _ List.mem_cons_self)
  have flatObject : isObjectPattern (.collection .hashBag (inner ++ others) none) = true :=
    isObject_bag.mpr fun element member => (List.mem_append.mp member).elim (innerObjects element)
      (fun inOthers => objects element (List.mem_cons_of_mem _ inOthers))
  -- equivalences of bags
  have permuted : ∀ {list list' : List Pattern}, list.Perm list' →
      HasType ccsRecCalc free bound (.collection .hashBag list none) (.base "Proc") →
      HasType ccsRecCalc free bound (.collection .hashBag list' none) (.base "Proc") ∧
        EquationEquiv (engineBasePremises RelationEnv.empty) ccsRecCalc (.collection .hashBag list none)
          (.collection .hashBag list' none) :=
    fun perm listTyped => ⟨typed_of_members listTyped fun element member => perm.mem_iff.mpr member,
      bag_result_equivalent perm listTyped⟩
  have flattened : ∀ {front inner' back : List Pattern},
      HasType ccsRecCalc free bound (.collection .hashBag (front ++ .collection .hashBag inner' none :: back) none)
        (.base "Proc") →
      HasType ccsRecCalc free bound (.collection .hashBag (front ++ inner' ++ back) none) (.base "Proc") ∧
        EquationEquiv (engineBasePremises RelationEnv.empty) ccsRecCalc
          (.collection .hashBag (front ++ .collection .hashBag inner' none :: back) none)
          (.collection .hashBag (front ++ inner' ++ back) none) := by
    intro front inner' back nestedBagTyped
    have derived := ccsRecBlockLanguage.flatten nestedBagTyped
    exact ⟨derived_typed_forward (block := ccsBlock) derived nestedBagTyped, derivedInstance_equivalent derived⟩
  constructor
  · intro action target step
    obtain ⟨targetTyped, -⟩ := step.typed admitted typed object
    obtain ⟨result, move, rfl⟩ := bagMove_of_step step
    rcases move.result_cases with ⟨member, rest, moved, perm, memberStep, rfl⟩ |
      ⟨first, second, rest, moved, moved', name, perm, firstStep, secondStep, rfl, rfl⟩
    · by_cases isNested : member = .collection .hashBag inner none
      · subst isNested
        have restPerm : others.Perm rest := perm.cons_inv
        obtain ⟨innerResult, innerMove, rfl⟩ := bagMove_of_step memberStep
        obtain ⟨result', step', resultPerm⟩ := step_of_bagMove (innerMove.extend others) none
        refine ⟨_, step', ?_⟩
        obtain ⟨typed₁, same₁⟩ := flattened (front := []) (inner' := innerResult) (back := rest) (by simpa using targetTyped)
        simp only [List.nil_append] at typed₁ same₁
        obtain ⟨typed₂, same₂⟩ := permuted (show (innerResult ++ rest).Perm result' by
          exact (restPerm.symm.append_left innerResult).trans resultPerm.symm) typed₁
        exact .trans _ _ _ same₁ same₂
      · obtain ⟨rest', restPerm, othersPerm⟩ := perm_cons_cons_of_ne perm isNested
        have flatPerm : (inner ++ others).Perm (member :: (inner ++ rest')) :=
          (othersPerm.append_left inner).trans List.perm_middle
        obtain ⟨result', step', resultPerm⟩ := step_of_bagMove (.one flatPerm memberStep) none
        refine ⟨_, step', ?_⟩
        obtain ⟨typed₁, same₁⟩ := permuted (restPerm.cons moved) targetTyped
        obtain ⟨typed₂, same₂⟩ := flattened (front := [moved]) (inner' := inner) (back := rest') (by simpa using typed₁)
        simp only [List.singleton_append] at typed₂ same₂
        obtain ⟨-, same₃⟩ := permuted (show (moved :: (inner ++ rest')).Perm result' by
          simpa using resultPerm.symm) (by simpa using typed₂)
        exact .trans _ _ _ same₁ (.trans _ _ _ (by simp only [List.cons_append] at same₂; exact same₂) same₃)
    · by_cases firstNested : first = .collection .hashBag inner none
      · subst firstNested
        obtain ⟨innerResult, innerMove, rfl⟩ := bagMove_of_step firstStep
        rcases innerMove.result_cases with ⟨element, inner', elementMoved, innerPerm, elementStep, rfl⟩ |
          ⟨_, _, _, _, _, _, _, _, _, absurd, _⟩
        · have othersPerm : others.Perm (second :: rest) := perm.cons_inv
          have flatPerm : (inner ++ others).Perm (element :: second :: (inner' ++ rest)) := by
            refine (innerPerm.append othersPerm).trans ?_
            perm_ac
          obtain ⟨result', step', resultPerm⟩ := step_of_bagMove (.two flatPerm elementStep secondStep) none
          refine ⟨_, step', ?_⟩
          obtain ⟨typed₁, same₁⟩ := flattened (front := []) (inner' := elementMoved :: inner') (back := moved' :: rest)
            (by simpa using targetTyped)
          simp only [List.nil_append] at typed₁ same₁
          obtain ⟨-, same₂⟩ := permuted (show (elementMoved :: inner' ++ moved' :: rest).Perm result' by
            refine List.Perm.trans ?_ resultPerm.symm
            perm_ac) typed₁
          exact .trans _ _ _ same₁ same₂
        · cases absurd
      · by_cases secondNested : second = .collection .hashBag inner none
        · subst secondNested
          obtain ⟨innerResult, innerMove, rfl⟩ := bagMove_of_step secondStep
          rcases innerMove.result_cases with ⟨element, inner', elementMoved, innerPerm, elementStep, rfl⟩ |
            ⟨_, _, _, _, _, _, _, _, _, absurd, _⟩
          · have swapped : (Pattern.collection .hashBag inner none :: others).Perm
                (Pattern.collection .hashBag inner none :: first :: rest) := perm.trans (List.Perm.swap _ _ _)
            have othersPerm : others.Perm (first :: rest) := swapped.cons_inv
            have flatPerm : (inner ++ others).Perm (first :: element :: (inner' ++ rest)) := by
              refine (innerPerm.append othersPerm).trans ?_
              perm_ac
            obtain ⟨result', step', resultPerm⟩ := step_of_bagMove (.two flatPerm firstStep elementStep) none
            refine ⟨_, step', ?_⟩
            obtain ⟨typed₁, same₁⟩ := flattened (front := [moved]) (inner' := elementMoved :: inner') (back := rest)
              (by simpa using targetTyped)
            simp only [List.singleton_append] at typed₁ same₁
            obtain ⟨-, same₂⟩ := permuted (show (moved :: (elementMoved :: inner' ++ rest)).Perm result' by
              refine List.Perm.trans ?_ resultPerm.symm
              perm_ac) (by simpa using typed₁)
            exact .trans _ _ _ (by simp only [List.cons_append] at same₁; exact same₁) same₂
          · cases absurd
        · obtain ⟨rest₁, restPerm₁, othersPerm₁⟩ := perm_cons_cons_of_ne perm firstNested
          obtain ⟨rest₂, restPerm₂, restPerm₁'⟩ := perm_cons_cons_of_ne restPerm₁.symm secondNested
          have flatPerm : (inner ++ others).Perm (first :: second :: (inner ++ rest₂)) := by
            refine ((othersPerm₁.trans (restPerm₁'.cons first)).append_left inner).trans ?_
            perm_ac
          obtain ⟨result', step', resultPerm⟩ := step_of_bagMove (.two flatPerm firstStep secondStep) none
          refine ⟨_, step', ?_⟩
          obtain ⟨typed₁, same₁⟩ := permuted ((restPerm₂.cons moved').cons moved) targetTyped
          obtain ⟨typed₂, same₂⟩ := flattened (front := [moved, moved']) (inner' := inner) (back := rest₂)
            (by simpa using typed₁)
          obtain ⟨-, same₃⟩ := permuted (show ([moved, moved'] ++ inner ++ rest₂).Perm result' by
            refine List.Perm.trans ?_ resultPerm.symm
            perm_ac) typed₂
          exact .trans _ _ _ same₁ (.trans _ _ _ (by simp only [List.cons_append, List.nil_append] at same₂; exact same₂) same₃)
  · intro action target step
    obtain ⟨targetTyped, -⟩ := step.typed admitted flatTyped flatObject
    obtain ⟨result, move, rfl⟩ := bagMove_of_step step
    have nestedLeaves : ∀ {innerResult : List Pattern} {action' : Action},
        BagMove definitions inner action' innerResult →
        ∃ innerResult', LStep definitions (.collection .hashBag inner none) action'
          (.collection .hashBag innerResult' none) ∧ innerResult'.Perm innerResult :=
      fun innerMove => step_of_bagMove innerMove none
    rcases move.result_cases with ⟨member, rest, moved, perm, memberStep, rfl⟩ |
      ⟨first, second, rest, moved, moved', name, perm, firstStep, secondStep, rfl, rfl⟩
    · by_cases inInner : member ∈ inner
      · have innerPerm := List.perm_cons_erase inInner
        have restPerm : rest.Perm (inner.erase member ++ others) :=
          (perm.symm.trans (innerPerm.append_right others)).cons_inv
        obtain ⟨innerResult', nestedStep, innerResultPerm⟩ := nestedLeaves (.one innerPerm memberStep)
        obtain ⟨result', step', resultPerm⟩ := step_of_bagMove
          (.one (List.Perm.refl (Pattern.collection .hashBag inner none :: others)) nestedStep) none
        refine ⟨_, step', ?_⟩
        obtain ⟨typed₁, same₁⟩ := permuted (show (moved :: rest).Perm (innerResult' ++ others) by
          refine List.Perm.trans ?_ (innerResultPerm.symm.append_right others)
          exact (restPerm.cons moved)) targetTyped
        have resultTyped := (step'.typed admitted typed object).1
        obtain ⟨typedNested, -⟩ := permuted resultPerm resultTyped
        obtain ⟨-, same₂⟩ := flattened (front := []) (inner' := innerResult') (back := others) (by simpa using typedNested)
        simp only [List.nil_append] at same₂
        obtain ⟨-, same₃⟩ := permuted resultPerm resultTyped
        exact .trans _ _ _ same₁ (.trans _ _ _ (.symm _ _ same₂) (.symm _ _ same₃))
      · have inOthers : member ∈ others := by
          have := perm.mem_iff.mpr List.mem_cons_self
          rcases List.mem_append.mp this with inInner' | inOthers
          · exact absurd inInner' inInner
          · exact inOthers
        have othersPerm := List.perm_cons_erase inOthers
        have restPerm : rest.Perm (inner ++ others.erase member) :=
          (perm.symm.trans ((othersPerm.append_left inner).trans List.perm_middle)).cons_inv
        obtain ⟨result', step', resultPerm⟩ := step_of_bagMove
          (.one ((othersPerm.cons _).trans (List.Perm.swap _ _ _)) memberStep) none
        refine ⟨_, step', ?_⟩
        have resultTyped := (step'.typed admitted typed object).1
        obtain ⟨typedFlat, same₁⟩ := permuted (restPerm.cons moved) targetTyped
        obtain ⟨typedNested, -⟩ := permuted resultPerm resultTyped
        obtain ⟨-, same₂⟩ := flattened (front := [moved]) (inner' := inner) (back := others.erase member)
          (by simpa using typedNested)
        simp only [List.singleton_append] at same₂
        obtain ⟨-, same₃⟩ := permuted resultPerm resultTyped
        exact .trans _ _ _ same₁ (.trans _ _ _ (.symm _ _ (by simp only [List.cons_append] at same₂; exact same₂)) (.symm _ _ same₃))
    · have resultsBack : ∀ {front back nested result' : List Pattern},
          (moved :: moved' :: rest).Perm (front ++ nested ++ back) →
          result'.Perm (front ++ Pattern.collection .hashBag nested none :: back) →
          HasType ccsRecCalc free bound (.collection .hashBag result' none) (.base "Proc") →
          EquationEquiv (engineBasePremises RelationEnv.empty) ccsRecCalc
            (.collection .hashBag (moved :: moved' :: rest) none) (.collection .hashBag result' none) := by
        intro front back nested result' flatPerm resultPerm resultTyped
        obtain ⟨-, same₁⟩ := permuted flatPerm targetTyped
        obtain ⟨typedNested, same₃⟩ := permuted resultPerm resultTyped
        obtain ⟨-, same₂⟩ := flattened (front := front) (inner' := nested) (back := back) typedNested
        exact .trans _ _ _ same₁ (.trans _ _ _ (.symm _ _ same₂) (.symm _ _ same₃))
      by_cases firstInner : first ∈ inner
      · have innerPerm₁ := List.perm_cons_erase firstInner
        have secondRest : (second :: rest).Perm (inner.erase first ++ others) :=
          (perm.symm.trans (innerPerm₁.append_right others)).cons_inv
        by_cases secondInner : second ∈ inner.erase first
        · have innerPerm₂ := List.perm_cons_erase secondInner
          have restPerm : rest.Perm ((inner.erase first).erase second ++ others) :=
            (secondRest.trans (innerPerm₂.append_right others)).cons_inv
          obtain ⟨innerResult', nestedStep, innerResultPerm⟩ :=
            nestedLeaves (.two (innerPerm₁.trans (innerPerm₂.cons first)) firstStep secondStep)
          obtain ⟨result', step', resultPerm⟩ := step_of_bagMove
            (.one (List.Perm.refl (Pattern.collection .hashBag inner none :: others)) nestedStep) none
          refine ⟨_, step', resultsBack (front := []) (back := others) (nested := innerResult') ?_ (by simpa using resultPerm)
            (step'.typed admitted typed object).1⟩
          refine List.Perm.trans ?_ (innerResultPerm.symm.append_right others)
          refine ((restPerm.cons moved').cons moved).trans ?_
          perm_ac
        · have secondOthers : second ∈ others := by
            have := secondRest.mem_iff.mp List.mem_cons_self
            rcases List.mem_append.mp this with inInner' | inOthers
            · exact absurd inInner' secondInner
            · exact inOthers
          have othersPerm := List.perm_cons_erase secondOthers
          have restPerm : rest.Perm (inner.erase first ++ others.erase second) :=
            (secondRest.trans ((othersPerm.append_left _).trans List.perm_middle)).cons_inv
          obtain ⟨innerResult', nestedStep, innerResultPerm⟩ := nestedLeaves (.one innerPerm₁ firstStep)
          obtain ⟨result', step', resultPerm⟩ := step_of_bagMove
            (.two (othersPerm.cons _) nestedStep secondStep) none
          refine ⟨_, step', resultsBack (front := []) (back := moved' :: others.erase second) (nested := innerResult')
            ?_ (by simpa using resultPerm) (step'.typed admitted typed object).1⟩
          refine List.Perm.trans ?_ (innerResultPerm.symm.append_right _)
          refine ((restPerm.cons moved').cons moved).trans ?_
          perm_ac
      · have firstOthers : first ∈ others := by
          have := perm.mem_iff.mpr List.mem_cons_self
          rcases List.mem_append.mp this with inInner' | inOthers
          · exact absurd inInner' firstInner
          · exact inOthers
        have othersPerm₁ := List.perm_cons_erase firstOthers
        have secondRest : (second :: rest).Perm (inner ++ others.erase first) :=
          (perm.symm.trans ((othersPerm₁.append_left inner).trans List.perm_middle)).cons_inv
        by_cases secondInner : second ∈ inner
        · have innerPerm := List.perm_cons_erase secondInner
          have restPerm : rest.Perm (inner.erase second ++ others.erase first) :=
            (secondRest.trans (innerPerm.append_right _)).cons_inv
          obtain ⟨innerResult', nestedStep, innerResultPerm⟩ := nestedLeaves (.one innerPerm secondStep)
          obtain ⟨result', step', resultPerm⟩ := step_of_bagMove
            (.two ((othersPerm₁.cons _).trans (List.Perm.swap _ _ _)) firstStep nestedStep) none
          refine ⟨_, step', resultsBack (front := [moved]) (back := others.erase first) (nested := innerResult')
            ?_ (by simpa using resultPerm) (step'.typed admitted typed object).1⟩
          have innerSide : (moved' :: inner.erase second).Perm innerResult' := innerResultPerm.symm
          refine ((restPerm.cons moved').cons moved).trans ?_
          exact (List.Perm.trans (by perm_ac) ((innerSide.append_right (others.erase first)).cons moved)).trans
            (by perm_ac)
        · have secondOthers : second ∈ others.erase first := by
            have := secondRest.mem_iff.mp List.mem_cons_self
            rcases List.mem_append.mp this with inInner' | inOthers
            · exact absurd inInner' secondInner
            · exact inOthers
          have othersPerm₂ := List.perm_cons_erase secondOthers
          have restPerm : rest.Perm (inner ++ (others.erase first).erase second) :=
            (secondRest.trans ((othersPerm₂.append_left inner).trans List.perm_middle)).cons_inv
          have bagPerm : (Pattern.collection .hashBag inner none :: others).Perm
              (first :: second :: Pattern.collection .hashBag inner none :: (others.erase first).erase second) := by
            refine ((othersPerm₁.trans (othersPerm₂.cons first)).cons _).trans ?_
            perm_ac
          obtain ⟨result', step', resultPerm⟩ := step_of_bagMove (.two bagPerm firstStep secondStep) none
          refine ⟨_, step', resultsBack (front := [moved, moved']) (back := (others.erase first).erase second)
            (nested := inner) ?_ (by simpa using resultPerm) (step'.typed admitted typed object).1⟩
          refine ((restPerm.cons moved').cons moved).trans ?_
          perm_ac

/-! ## Restriction -/

/-- A name of an action of a typed process is a variable. -/
def Action.named : Action → Prop
  | .act name | .coact name => (∃ index, name = .bvar index) ∨ ∃ held, name = .fvar held
  | .tau => True

/-- **The names of a typed process's actions are variables.** -/
theorem LStep.named (admitted : admits definitions = true) {source : Pattern} {action : Action} {target : Pattern}
    (step : LStep definitions source action target) :
    ∀ {free : FreeTypeContext} {bound : List TypeExpr}, HasType ccsRecCalc free bound source (.base "Proc") →
      isObjectPattern source = true → action.named := by
  induction step with
  | @offer component guards offered k hk action continuation performs =>
      intro free bound typed object
      have guardTyped := offers_guards_typed admitted typed offered _ (List.getElem_mem hk)
      have guardObject := offers_guards_objects admitted object offered _ (List.getElem_mem hk)
      rcases guardAction_some performs with ⟨name, rfl, guardIs⟩ | ⟨name, rfl, guardIs⟩ | ⟨rfl, -⟩
      · rw [guardIs] at guardTyped guardObject
        have nameObject : isObjectPattern name = true := by
          simp only [isObjectPattern, isObjectPatternList, Bool.and_true, Bool.and_eq_true] at guardObject
          exact guardObject.1
        exact name_variable (prefix_parts (.inl rfl) guardTyped).1 nameObject
      · rw [guardIs] at guardTyped guardObject
        have nameObject : isObjectPattern name = true := by
          simp only [isObjectPattern, isObjectPatternList, Bool.and_true, Bool.and_eq_true] at guardObject
          exact guardObject.1
        exact name_variable (prefix_parts (.inr rfl) guardTyped).1 nameObject
      · trivial
  | @par elements tail i hi action target inner recurse =>
      intro free bound typed object
      cases bag_tail_none object
      exact recurse (members_of_bag (block := ccsBlock) typed _ (List.getElem_mem hi))
        (bag_objects object _ (List.getElem_mem hi))
  | sync => intro _ _ _ _; trivial
  | @res binder source target action action' inner seen recurse =>
      intro free bound typed object
      cases restriction_binder (block := ccsBlock) typed
      have bodyObject : isObjectPattern source = true := by rwa [isObject_restriction] at object
      have inner' := recurse (restriction_body (block := ccsBlock) typed) bodyObject
      have lowered : ∀ {name name' : Pattern}, ((∃ index, name = .bvar index) ∨ ∃ held, name = .fvar held) →
          lowerName? name = some name' → (∃ index, name' = .bvar index) ∨ ∃ held, name' = .fvar held := by
        intro name name' variable' found
        rcases variable' with ⟨index, rfl⟩ | ⟨held, rfl⟩
        · cases index with
          | zero => simp [lowerName?] at found
          | succ index => simp only [lowerName?, Option.some.injEq] at found; exact .inl ⟨index, found.symm⟩
        · simp only [lowerName?, Option.some.injEq] at found; exact .inr ⟨held, found.symm⟩
      cases action with
      | act name =>
          obtain ⟨name', found, rfl⟩ := Option.map_eq_some_iff.mp seen
          exact lowered inner' found
      | coact name =>
          obtain ⟨name', found, rfl⟩ := Option.map_eq_some_iff.mp seen
          exact lowered inner' found
      | tau =>
          simp only [Action.lower?, Option.some.injEq] at seen
          subst seen
          trivial

theorem Action.lower?_lift_one {action : Action} (named : action.named) : (action.lift 1).lower? = some action := by
  have lowered : ∀ {name : Pattern}, ((∃ index, name = .bvar index) ∨ ∃ held, name = .fvar held) →
      lowerName? (liftBVars 0 1 name) = some name := by
    intro name variable'
    rcases variable' with ⟨index, rfl⟩ | ⟨held, rfl⟩
    · simp [liftBVars, lowerName?]
    · simp [liftBVars, lowerName?]
  cases action with
  | act name => simp [Action.lift, Action.lower?, lowered named]
  | coact name => simp [Action.lift, Action.lower?, lowered named]
  | tau => rfl

theorem Action.rename_shift (action : Action) : action.rename (shiftAbove 0 1) = action.lift 1 := by
  cases action <;> simp [Action.rename, Action.lift, liftBVars_eq_rename]

theorem Action.lift_injective {first second : Action} {count : Nat} (same : first.lift count = second.lift count) :
    first = second := by
  have injective : Function.Injective (liftBVars 0 count) := by
    have isRename : (liftBVars 0 count : Pattern → Pattern) =
        Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename (shiftAbove 0 count) :=
      funext (liftBVars_eq_rename 0 count)
    rw [isRename]
    apply rename_injective
    intro first second equal
    simp only [shiftAbove, Nat.not_lt_zero, if_false] at equal
    omega
  cases first <;> cases second <;> simp only [Action.lift, Action.act.injEq, Action.coact.injEq, reduceCtorEq] at same
  · rw [injective same]
  · rw [injective same]
  · rfl

/-- **A restriction moves when its body does**, the action seen outside it. -/
theorem lstep_restriction_inv {binder : Option String} {body : Pattern} {action : Action} {target : Pattern}
    (step : LStep definitions (.apply "CNu" [.lambda binder body]) action target) :
    ∃ action' target', LStep definitions body action' target' ∧ action'.lower? = some action ∧
      target = .apply "CNu" [.lambda none target'] := by
  generalize sourceIs : Pattern.apply "CNu" [.lambda binder body] = source at step
  cases step with
  | offer offered => subst sourceIs; simp [offers] at offered
  | par => cases sourceIs
  | sync => cases sourceIs
  | res _ inner seen =>
      simp only [Pattern.apply.injEq, List.cons.injEq, Pattern.lambda.injEq, and_true, true_and] at sourceIs
      obtain ⟨-, rfl⟩ := sourceIs
      exact ⟨_, _, inner, seen, rfl⟩

theorem LStep.lift (admitted : admits definitions = true) {source : Pattern} {action : Action} {target : Pattern}
    (step : LStep definitions source action target) :
    LStep definitions (liftBVars 0 1 source) (action.lift 1) (liftBVars 0 1 target) := by
  have lifted := step.rename admitted (shiftAbove 0 1)
  rwa [← liftBVars_eq_rename, ← liftBVars_eq_rename, Action.rename_shift] at lifted

theorem LStep.lift_inv (admitted : admits definitions = true) {source : Pattern} {action' : Action}
    {target' : Pattern} (step : LStep definitions (liftBVars 0 1 source) action' target') :
    ∃ action target, LStep definitions source action target ∧ action' = action.lift 1 ∧
      target' = liftBVars 0 1 target := by
  have injective : Function.Injective (shiftAbove 0 1) := by
    intro first second equal
    simp only [shiftAbove, Nat.not_lt_zero, if_false] at equal
    omega
  rw [liftBVars_eq_rename] at step
  obtain ⟨action, target, step', rfl, rfl⟩ := step.rename_inv admitted injective rfl
  exact ⟨action, target, step', Action.rename_shift action, (liftBVars_eq_rename 0 1 target).symm⟩

/-- **A restriction in a bag matches the restriction of the bag**: scope extrusion keeps transitions. -/
theorem matched_extrusion (admitted : admits definitions = true) {free : FreeTypeContext} {bound : List TypeExpr}
    {body : Pattern} {others : List Pattern}
    (bodyTyped : HasType ccsRecCalc free (.base "Name" :: bound) body (.base "Proc"))
    (bodyObject : isObjectPattern body = true)
    (othersMembers : Members ccsRecCalc ccsBlock free bound others)
    (othersObjects : ∀ element ∈ others, isObjectPattern element = true) :
    Matched definitions (.collection .hashBag (.apply "CNu" [.lambda none body] :: others) none)
        (.apply "CNu" [.lambda none (.collection .hashBag (body :: others.map (liftBVars 0 1)) none)]) ∧
      Matched definitions (.apply "CNu" [.lambda none (.collection .hashBag (body :: others.map (liftBVars 0 1)) none)])
        (.collection .hashBag (.apply "CNu" [.lambda none body] :: others) none) := by
  have nuTyped : HasType ccsRecCalc free bound (.apply "CNu" [.lambda none body]) (.base "Proc") :=
    ccsRecBlockLanguage.restrict_typed bodyTyped
  have bagTyped : HasType ccsRecCalc free bound (.collection .hashBag (.apply "CNu" [.lambda none body] :: others) none)
      (.base "Proc") := bag_typed (block := ccsBlock) (rest := none) fun element member =>
    (List.mem_cons.mp member).elim (fun same => same ▸ nuTyped) (othersMembers element)
  have bagObject : isObjectPattern (.collection .hashBag (.apply "CNu" [.lambda none body] :: others) none) = true :=
    isObject_bag.mpr fun element member => (List.mem_cons.mp member).elim
      (fun same => by rw [same, isObject_restriction]; exact bodyObject) (othersObjects element)
  have liftedMembers := lift_members 1 othersMembers
  have insideTyped : HasType ccsRecCalc free (.base "Name" :: bound)
      (.collection .hashBag (body :: others.map (liftBVars 0 1)) none) (.base "Proc") :=
    bag_typed (block := ccsBlock) (rest := none) fun element member =>
      (List.mem_cons.mp member).elim (fun same => same ▸ bodyTyped) (by simpa using liftedMembers element)
  have insideObject : isObjectPattern (.collection .hashBag (body :: others.map (liftBVars 0 1)) none) = true :=
    isObject_bag.mpr fun element member => (List.mem_cons.mp member).elim (fun same => same ▸ bodyObject) (by
      intro lifted
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp lifted
      rw [isObject_liftBVars]
      exact othersObjects original originalMember)
  have restrictedTyped : HasType ccsRecCalc free bound
      (.apply "CNu" [.lambda none (.collection .hashBag (body :: others.map (liftBVars 0 1)) none)]) (.base "Proc") :=
    ccsRecBlockLanguage.restrict_typed insideTyped
  have restrictedObject : isObjectPattern
      (.apply "CNu" [.lambda none (.collection .hashBag (body :: others.map (liftBVars 0 1)) none)]) = true := by
    rw [isObject_restriction]; exact insideObject
  -- equivalences
  have extruded : ∀ {inner : Pattern} {list : List Pattern},
      HasType ccsRecCalc free (.base "Name" :: bound) inner (.base "Proc") →
      Members ccsRecCalc ccsBlock free bound list →
      EquationEquiv (engineBasePremises RelationEnv.empty) ccsRecCalc
        (.collection .hashBag (.apply "CNu" [.lambda none inner] :: list) none)
        (.apply "CNu" [.lambda none (.collection .hashBag (inner :: list.map (liftBVars 0 1)) none)]) :=
    fun innerTyped listMembers => (extrusion_equivalent (block := ccsBlock) innerTyped listMembers).toEquationEquiv
  have permuted : ∀ {context : List TypeExpr} {list list' : List Pattern}, list.Perm list' →
      HasType ccsRecCalc free context (.collection .hashBag list none) (.base "Proc") →
      EquationEquiv (engineBasePremises RelationEnv.empty) ccsRecCalc (.collection .hashBag list none)
        (.collection .hashBag list' none) :=
    fun perm listTyped => bag_result_equivalent perm listTyped
  have nuPermuted : ∀ {list list' : List Pattern}, list.Perm list' →
      HasType ccsRecCalc free (.base "Name" :: bound) (.collection .hashBag list none) (.base "Proc") →
      EquationEquiv (engineBasePremises RelationEnv.empty) ccsRecCalc
        (.apply "CNu" [.lambda none (.collection .hashBag list none)])
        (.apply "CNu" [.lambda none (.collection .hashBag list' none)]) :=
    fun perm listTyped => restricts_equation (language := ccsRecCalc) (block := ccsBlock) 1 (permuted perm listTyped)
  have bagMembersOf : ∀ {context : List TypeExpr} {list : List Pattern},
      HasType ccsRecCalc free context (.collection .hashBag list none) (.base "Proc") →
      Members ccsRecCalc ccsBlock free context list := fun listTyped => members_of_bag (block := ccsBlock) listTyped
  constructor
  · intro action target step
    obtain ⟨targetTyped, -⟩ := step.typed admitted bagTyped bagObject
    obtain ⟨result, move, rfl⟩ := bagMove_of_step step
    have targetMembers := bagMembersOf targetTyped
    rcases move.result_cases with ⟨member, rest, moved, perm, memberStep, rfl⟩ |
      ⟨first, second, rest, moved, moved', name, perm, firstStep, secondStep, rfl, rfl⟩
    · by_cases isRestricted : member = .apply "CNu" [.lambda none body]
      · subst isRestricted
        have restPerm : others.Perm rest := perm.cons_inv
        obtain ⟨inner, innerTarget, innerStep, seen, rfl⟩ := lstep_restriction_inv memberStep
        obtain ⟨result', step', resultPerm⟩ := step_of_bagMove (definitions := definitions)
          (.one (List.Perm.refl (body :: others.map (liftBVars 0 1))) innerStep) none
        refine ⟨_, .res none step' seen, ?_⟩
        have innerTyped := (innerStep.typed admitted bodyTyped bodyObject).1
        have movedTyped := targetMembers _ List.mem_cons_self
        have restMembers : Members ccsRecCalc ccsBlock free bound rest :=
          fun element member => targetMembers element (List.mem_cons_of_mem _ member)
        refine .trans _ _ _ (extruded innerTyped restMembers) (nuPermuted ?_ ?_)
        · exact ((restPerm.symm.map (liftBVars 0 1)).cons innerTarget).trans resultPerm.symm
        · exact bag_typed (block := ccsBlock) (rest := none) fun element member =>
            (List.mem_cons.mp member).elim (fun same => same ▸ innerTyped)
              (fun lifted => by simpa using lift_members 1 restMembers element lifted)
      · obtain ⟨rest', restPerm, othersPerm⟩ := perm_cons_cons_of_ne perm isRestricted
        have memberTyped := othersMembers member (othersPerm.mem_iff.mpr List.mem_cons_self)
        have memberObject := othersObjects member (othersPerm.mem_iff.mpr List.mem_cons_self)
        have named := memberStep.named admitted memberTyped memberObject
        have insidePerm : (body :: others.map (liftBVars 0 1)).Perm
            (liftBVars 0 1 member :: body :: rest'.map (liftBVars 0 1)) := by
          refine ((othersPerm.map (liftBVars 0 1)).cons body).trans ?_
          simp only [List.map_cons]
          exact List.Perm.swap _ _ _
        obtain ⟨result', step', resultPerm⟩ := step_of_bagMove (.one insidePerm (memberStep.lift admitted)) none
        refine ⟨_, .res none step' (Action.lower?_lift_one named), ?_⟩
        have targetOrdered := permuted ((restPerm.cons moved).trans (List.Perm.swap _ _ _)) targetTyped
        have orderedTyped : HasType ccsRecCalc free bound
            (.collection .hashBag (.apply "CNu" [.lambda none body] :: moved :: rest') none) (.base "Proc") :=
          typed_of_members targetTyped fun element member =>
            ((restPerm.cons moved).trans (List.Perm.swap _ _ _)).mem_iff.mpr member
        have orderedMembers := bagMembersOf orderedTyped
        have extrudedTarget := extruded (list := moved :: rest') bodyTyped
          (fun element member => orderedMembers element (List.mem_cons_of_mem _ member))
        refine .trans _ _ _ targetOrdered (.trans _ _ _ extrudedTarget (nuPermuted ?_ ?_))
        · refine List.Perm.trans ?_ resultPerm.symm
          simp only [List.map_cons]
          exact List.Perm.swap _ _ _
        · exact bag_typed (block := ccsBlock) (rest := none) fun element member =>
            (List.mem_cons.mp member).elim (fun same => same ▸ bodyTyped) (fun lifted => by
              simpa using lift_members 1 (fun element member => orderedMembers element (List.mem_cons_of_mem _ member))
                element lifted)
    · have liftedTyped : ∀ {list : List Pattern}, Members ccsRecCalc ccsBlock free bound list →
          ∀ {inner : Pattern}, HasType ccsRecCalc free (.base "Name" :: bound) inner (.base "Proc") →
          HasType ccsRecCalc free (.base "Name" :: bound)
            (.collection .hashBag (inner :: list.map (liftBVars 0 1)) none) (.base "Proc") :=
        by
          intro list listMembers inner innerTyped
          exact bag_typed (block := ccsBlock) (rest := none) fun element member =>
            (List.mem_cons.mp member).elim (fun same => same ▸ innerTyped)
              (fun lifted => by simpa using lift_members 1 listMembers element lifted)
      by_cases firstRestricted : first = .apply "CNu" [.lambda none body]
      · subst firstRestricted
        have othersPerm : others.Perm (second :: rest) := perm.cons_inv
        obtain ⟨inner, innerTarget, innerStep, seen, rfl⟩ := lstep_restriction_inv firstStep
        have innerIs : inner = (Action.act name).lift 1 := Action.lower?_some seen
        subst innerIs
        have insidePerm : (body :: others.map (liftBVars 0 1)).Perm
            (body :: liftBVars 0 1 second :: rest.map (liftBVars 0 1)) := by
          simpa using (othersPerm.map (liftBVars 0 1)).cons body
        obtain ⟨result', step', resultPerm⟩ := step_of_bagMove (.two insidePerm innerStep (secondStep.lift admitted)) none
        refine ⟨_, .res none step' rfl, ?_⟩
        have innerTyped := (innerStep.typed admitted bodyTyped bodyObject).1
        have listMembers : Members ccsRecCalc ccsBlock free bound (moved' :: rest) :=
          fun element member => targetMembers element (List.mem_cons_of_mem _ member)
        refine .trans _ _ _ (extruded innerTyped listMembers) (nuPermuted ?_ (liftedTyped listMembers innerTyped))
        simpa using resultPerm.symm
      · by_cases secondRestricted : second = .apply "CNu" [.lambda none body]
        · subst secondRestricted
          have othersPerm : others.Perm (first :: rest) := (perm.trans (List.Perm.swap _ _ _)).cons_inv
          obtain ⟨inner, innerTarget, innerStep, seen, rfl⟩ := lstep_restriction_inv secondStep
          have innerIs : inner = (Action.coact name).lift 1 := Action.lower?_some seen
          subst innerIs
          have insidePerm : (body :: others.map (liftBVars 0 1)).Perm
              (liftBVars 0 1 first :: body :: rest.map (liftBVars 0 1)) := by
            refine ((othersPerm.map (liftBVars 0 1)).cons body).trans ?_
            simp only [List.map_cons]
            exact List.Perm.swap _ _ _
          obtain ⟨result', step', resultPerm⟩ := step_of_bagMove (.two insidePerm (firstStep.lift admitted) innerStep) none
          refine ⟨_, .res none step' rfl, ?_⟩
          have innerTyped := (innerStep.typed admitted bodyTyped bodyObject).1
          have listMembers : Members ccsRecCalc ccsBlock free bound (moved :: rest) := by
            intro element member
            rcases List.mem_cons.mp member with rfl | inRest
            · exact targetMembers _ List.mem_cons_self
            · exact targetMembers element (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ inRest))
          have reordered := permuted (List.Perm.swap (Pattern.apply "CNu" [.lambda none innerTarget]) moved rest)
            targetTyped
          refine .trans _ _ _ reordered (.trans _ _ _ (extruded innerTyped listMembers)
            (nuPermuted ?_ (liftedTyped listMembers innerTyped)))
          refine List.Perm.trans ?_ resultPerm.symm
          simp only [List.map_cons]
          exact List.Perm.swap _ _ _
        · obtain ⟨rest₁, restPerm₁, othersPerm₁⟩ := perm_cons_cons_of_ne perm firstRestricted
          obtain ⟨rest₂, restPerm₂, restPerm₁'⟩ := perm_cons_cons_of_ne restPerm₁.symm secondRestricted
          have othersPerm : others.Perm (first :: second :: rest₂) := othersPerm₁.trans (restPerm₁'.cons first)
          have insidePerm : (body :: others.map (liftBVars 0 1)).Perm
              (liftBVars 0 1 first :: liftBVars 0 1 second :: body :: rest₂.map (liftBVars 0 1)) := by
            refine ((othersPerm.map (liftBVars 0 1)).cons body).trans ?_
            simp only [List.map_cons]
            perm_ac
          obtain ⟨result', step', resultPerm⟩ := step_of_bagMove
            (.two insidePerm (firstStep.lift admitted) (secondStep.lift admitted)) none
          refine ⟨_, .res none step' rfl, ?_⟩
          have orderedPerm : (moved :: moved' :: rest).Perm
              (Pattern.apply "CNu" [.lambda none body] :: moved :: moved' :: rest₂) := by
            refine ((restPerm₂.cons moved').cons moved).trans ?_
            perm_ac
          have orderedTyped := typed_of_members targetTyped fun element member => orderedPerm.mem_iff.mpr member
          have orderedMembers := bagMembersOf orderedTyped
          have listMembers : Members ccsRecCalc ccsBlock free bound (moved :: moved' :: rest₂) :=
            fun element member => orderedMembers element (List.mem_cons_of_mem _ member)
          refine .trans _ _ _ (permuted orderedPerm targetTyped) (.trans _ _ _ (extruded bodyTyped listMembers)
            (nuPermuted ?_ (liftedTyped listMembers bodyTyped)))
          refine List.Perm.trans ?_ resultPerm.symm
          simp only [List.map_cons]
          perm_ac
  · intro action target step
    obtain ⟨inner, innerTarget, innerStep, seen, rfl⟩ := lstep_restriction_inv step
    have innerTargetTyped := (innerStep.typed admitted insideTyped insideObject).1
    obtain ⟨result, move, rfl⟩ := bagMove_of_step innerStep
    have resultMembers := bagMembersOf innerTargetTyped
    have backwards : ∀ {innerBody : Pattern} {list result' : List Pattern},
        HasType ccsRecCalc free (.base "Name" :: bound) innerBody (.base "Proc") →
        result.Perm (innerBody :: list.map (liftBVars 0 1)) →
        Members ccsRecCalc ccsBlock free bound list →
        result'.Perm (.apply "CNu" [.lambda none innerBody] :: list) →
        EquationEquiv (engineBasePremises RelationEnv.empty) ccsRecCalc
          (.apply "CNu" [.lambda none (.collection .hashBag result none)]) (.collection .hashBag result' none) := by
      intro innerBody list result' innerBodyTyped resultPerm listMembers result'Perm
      have listTyped : HasType ccsRecCalc free bound
          (.collection .hashBag (.apply "CNu" [.lambda none innerBody] :: list) none) (.base "Proc") :=
        bag_typed (block := ccsBlock) (rest := none) fun element member =>
          (List.mem_cons.mp member).elim (fun same => same ▸ ccsRecBlockLanguage.restrict_typed innerBodyTyped)
            (listMembers element)
      exact .trans _ _ _ (nuPermuted resultPerm innerTargetTyped) (.trans _ _ _
        (.symm _ _ (extruded innerBodyTyped listMembers)) (permuted result'Perm.symm listTyped))
    have liftedIn : ∀ {list : List Pattern} {element : Pattern}, element ∈ list.map (liftBVars 0 1) →
        ∃ original ∈ list, liftBVars 0 1 original = element := by
      intro list element member
      exact List.mem_map.mp member
    have erasedMembers : ∀ {list : List Pattern} {original : Pattern}, Members ccsRecCalc ccsBlock free bound list →
        Members ccsRecCalc ccsBlock free bound (list.erase original) :=
      fun listMembers element member => listMembers element (List.mem_of_mem_erase member)
    have erasedObjects : ∀ {list : List Pattern} {original : Pattern},
        (∀ element ∈ list, isObjectPattern element = true) →
        ∀ element ∈ list.erase original, isObjectPattern element = true :=
      fun listObjects element member => listObjects element (List.mem_of_mem_erase member)
    have consMembers : ∀ {head : Pattern} {list : List Pattern},
        HasType ccsRecCalc free bound head (.base "Proc") → Members ccsRecCalc ccsBlock free bound list →
        Members ccsRecCalc ccsBlock free bound (head :: list) :=
      fun headTyped listMembers element member => (List.mem_cons.mp member).elim (fun same => same ▸ headTyped)
        (listMembers element)
    have liftedErase : ∀ {list : List Pattern} {original : Pattern} {rest' : List Pattern},
        original ∈ list → (list.map (liftBVars 0 1)).Perm (liftBVars 0 1 original :: rest') →
        rest'.Perm ((list.erase original).map (liftBVars 0 1)) := by
      intro list original rest' originalMember liftedPerm
      have erased := (List.perm_cons_erase originalMember).map (liftBVars 0 1)
      exact (liftedPerm.symm.trans erased).cons_inv
    rcases move.result_cases with ⟨member, rest, moved, perm, memberStep, rfl⟩ |
      ⟨first, second, rest, moved, moved', name, perm, firstStep, secondStep, rfl, rfl⟩
    · by_cases isBody : member = body
      · subst isBody
        have restPerm : (others.map (liftBVars 0 1)).Perm rest := perm.cons_inv
        obtain ⟨result', step', resultPerm⟩ := step_of_bagMove
          (.one (List.Perm.refl (Pattern.apply "CNu" [.lambda none member] :: others)) (.res none memberStep seen)) none
        refine ⟨_, step', backwards (resultMembers moved List.mem_cons_self) (restPerm.symm.cons moved) othersMembers
          resultPerm⟩
      · obtain ⟨rest', restPerm, liftedPerm⟩ := perm_cons_cons_of_ne perm isBody
        obtain ⟨original, originalMember, rfl⟩ := liftedIn (liftedPerm.mem_iff.mpr List.mem_cons_self)
        obtain ⟨action₀, moved₀, originalStep, actionIs, rfl⟩ := memberStep.lift_inv admitted
        have same : action₀ = action := Action.lift_injective (actionIs.symm.trans (Action.lower?_some seen))
        subst same
        have othersPerm := List.perm_cons_erase originalMember
        have bagPerm : (Pattern.apply "CNu" [.lambda none body] :: others).Perm
            (original :: Pattern.apply "CNu" [.lambda none body] :: others.erase original) :=
          (othersPerm.cons _).trans (List.Perm.swap _ _ _)
        obtain ⟨result', step', resultPerm⟩ := step_of_bagMove (.one bagPerm originalStep) none
        refine ⟨_, step', ?_⟩
        have movedTyped := (originalStep.typed admitted (othersMembers original originalMember)
          (othersObjects original originalMember)).1
        refine backwards (list := moved₀ :: others.erase original) bodyTyped ?_
          (consMembers movedTyped (erasedMembers othersMembers)) (resultPerm.trans (List.Perm.swap _ _ _))
        refine ((restPerm.trans ((liftedErase originalMember liftedPerm).cons body)).cons _).trans ?_
        simp only [List.map_cons]
        exact List.Perm.swap _ _ _
    · have actionTau : action = .tau := by simpa [Action.lower?] using seen.symm
      subst actionTau
      by_cases firstBody : first = body
      · subst firstBody
        have secondPerm : (others.map (liftBVars 0 1)).Perm (second :: rest) := perm.cons_inv
        obtain ⟨original, originalMember, rfl⟩ := liftedIn (secondPerm.mem_iff.mpr List.mem_cons_self)
        obtain ⟨action₀, moved₀, originalStep, actionIs, rfl⟩ := secondStep.lift_inv admitted
        cases action₀ with
        | coact name₀ =>
            simp only [Action.lift, Action.coact.injEq] at actionIs
            subst actionIs
            have originalTyped := othersMembers original originalMember
            have originalObject := othersObjects original originalMember
            have named : (Action.act name₀).named := originalStep.named admitted originalTyped originalObject
            have firstNu : LStep definitions (.apply "CNu" [.lambda none first]) (.act name₀)
                (.apply "CNu" [.lambda none moved]) := .res none firstStep (Action.lower?_lift_one named)
            have bagPerm : (Pattern.apply "CNu" [.lambda none first] :: others).Perm
                (Pattern.apply "CNu" [.lambda none first] :: original :: others.erase original) :=
              (List.perm_cons_erase originalMember).cons _
            obtain ⟨result', step', resultPerm⟩ := step_of_bagMove (.two bagPerm firstNu originalStep) none
            refine ⟨_, step', ?_⟩
            have movedTyped := (originalStep.typed admitted originalTyped originalObject).1
            refine backwards (list := moved₀ :: others.erase original) (resultMembers moved List.mem_cons_self) ?_
              (consMembers movedTyped (erasedMembers othersMembers)) resultPerm
            simp only [List.map_cons]
            exact ((liftedErase originalMember secondPerm).cons _).cons _
        | act _ => simp [Action.lift] at actionIs
        | tau => simp [Action.lift] at actionIs
      · by_cases secondBody : second = body
        · subst secondBody
          have firstPerm : (others.map (liftBVars 0 1)).Perm (first :: rest) :=
            (perm.trans (List.Perm.swap _ _ _)).cons_inv
          obtain ⟨original, originalMember, rfl⟩ := liftedIn (firstPerm.mem_iff.mpr List.mem_cons_self)
          obtain ⟨action₀, moved₀, originalStep, actionIs, rfl⟩ := firstStep.lift_inv admitted
          cases action₀ with
          | act name₀ =>
              simp only [Action.lift, Action.act.injEq] at actionIs
              subst actionIs
              have originalTyped := othersMembers original originalMember
              have originalObject := othersObjects original originalMember
              have named : (Action.coact name₀).named := originalStep.named admitted originalTyped originalObject
              have secondNu : LStep definitions (.apply "CNu" [.lambda none second]) (.coact name₀)
                  (.apply "CNu" [.lambda none moved']) := .res none secondStep (Action.lower?_lift_one named)
              have bagPerm : (Pattern.apply "CNu" [.lambda none second] :: others).Perm
                  (original :: Pattern.apply "CNu" [.lambda none second] :: others.erase original) :=
                ((List.perm_cons_erase originalMember).cons _).trans (List.Perm.swap _ _ _)
              obtain ⟨result', step', resultPerm⟩ := step_of_bagMove (.two bagPerm originalStep secondNu) none
              refine ⟨_, step', ?_⟩
              have movedTyped := (originalStep.typed admitted originalTyped originalObject).1
              refine backwards (list := moved₀ :: others.erase original)
                (resultMembers moved' (List.mem_cons_of_mem _ List.mem_cons_self)) ?_
                (consMembers movedTyped (erasedMembers othersMembers)) (resultPerm.trans (List.Perm.swap _ _ _))
              simp only [List.map_cons]
              exact (((liftedErase originalMember firstPerm).cons _).cons _).trans (List.Perm.swap _ _ _)
          | coact _ => simp [Action.lift] at actionIs
          | tau => simp [Action.lift] at actionIs
        · obtain ⟨rest₁, restPerm₁, liftedPerm₁⟩ := perm_cons_cons_of_ne perm firstBody
          obtain ⟨rest₂, restPerm₂, restPerm₁'⟩ := perm_cons_cons_of_ne restPerm₁.symm secondBody
          have liftedPerm : (others.map (liftBVars 0 1)).Perm (first :: second :: rest₂) :=
            liftedPerm₁.trans (restPerm₁'.cons first)
          obtain ⟨original₁, originalMember₁, rfl⟩ := liftedIn (liftedPerm.mem_iff.mpr List.mem_cons_self)
          have afterFirst := liftedErase originalMember₁ liftedPerm
          obtain ⟨original₂, originalMember₂, rfl⟩ := liftedIn (afterFirst.mem_iff.mp List.mem_cons_self)
          have afterSecond := liftedErase originalMember₂ afterFirst.symm
          obtain ⟨action₁, moved₁, step₁, actionIs₁, rfl⟩ := firstStep.lift_inv admitted
          obtain ⟨action₂, moved₂, step₂, actionIs₂, rfl⟩ := secondStep.lift_inv admitted
          cases action₁ with
          | act name₁ =>
              cases action₂ with
              | coact name₂ =>
                  simp only [Action.lift, Action.act.injEq, Action.coact.injEq] at actionIs₁ actionIs₂
                  have sameName : name₁ = name₂ := by
                    have := Action.lift_injective (count := 1) (first := .act name₁) (second := .act name₂)
                      (by simp [Action.lift, ← actionIs₁, ← actionIs₂])
                    simpa using this
                  subst sameName
                  have bagPerm : (Pattern.apply "CNu" [.lambda none body] :: others).Perm
                      (original₁ :: original₂ :: Pattern.apply "CNu" [.lambda none body] ::
                        (others.erase original₁).erase original₂) := by
                    refine (((List.perm_cons_erase originalMember₁).trans
                      ((List.perm_cons_erase originalMember₂).cons original₁)).cons _).trans ?_
                    perm_ac
                  obtain ⟨result', step', resultPerm⟩ := step_of_bagMove (.two bagPerm step₁ step₂) none
                  refine ⟨_, step', ?_⟩
                  have typed₁ := othersMembers original₁ originalMember₁
                  have typed₂ := erasedMembers othersMembers original₂ originalMember₂
                  have moved₁Typed := (step₁.typed admitted typed₁ (othersObjects original₁ originalMember₁)).1
                  have moved₂Typed := (step₂.typed admitted typed₂
                    (erasedObjects othersObjects original₂ originalMember₂)).1
                  refine backwards (list := moved₁ :: moved₂ :: (others.erase original₁).erase original₂) bodyTyped ?_
                    (consMembers moved₁Typed (consMembers moved₂Typed (erasedMembers (erasedMembers othersMembers))))
                    (resultPerm.trans (by perm_ac))
                  refine ((restPerm₂.trans (afterSecond.cons body)).cons _ |>.cons _).trans ?_
                  simp only [List.map_cons]
                  perm_ac
              | act _ => simp [Action.lift] at actionIs₂
              | tau => simp [Action.lift] at actionIs₂
          | coact _ => simp [Action.lift] at actionIs₁
          | tau => simp [Action.lift] at actionIs₁

/-! ## Exchange of restrictions -/

theorem swapInner_injective : Function.Injective swapInner := fun first second same => by
  rw [← swapInner_swapInner first, same, swapInner_swapInner]

/-- Seen past two restrictions, an action and its exchanged renaming are the same. -/
theorem lower_lower_swap {inner middle outer : Action} (first : inner.lower? = some middle)
    (second : middle.lower? = some outer) :
    ∃ middle', (inner.rename swapInner).lower? = some middle' ∧ middle'.lower? = some outer := by
  have names : ∀ {name middleName outerName : Pattern}, lowerName? name = some middleName →
      lowerName? middleName = some outerName →
      ∃ middleName', lowerName? (rename swapInner name) = some middleName' ∧
        lowerName? middleName' = some outerName := by
    intro name middleName outerName firstLower secondLower
    match name, firstLower with
    | .bvar (index + 1), firstLower =>
        simp only [lowerName?, Option.some.injEq] at firstLower
        subst firstLower
        match index, secondLower with
        | index + 1, secondLower =>
            refine ⟨.bvar (index + 1), ?_, secondLower⟩
            simp [rename_bvar, swapInner, lowerName?]
    | .fvar held, firstLower =>
        simp only [lowerName?, Option.some.injEq] at firstLower
        subst firstLower
        exact ⟨.fvar held, by simp [rename_fvar, lowerName?], secondLower⟩
  cases inner with
  | act name =>
      obtain ⟨middleName, firstLower, rfl⟩ := Option.map_eq_some_iff.mp first
      obtain ⟨outerName, secondLower, rfl⟩ := Option.map_eq_some_iff.mp second
      obtain ⟨middleName', found, found'⟩ := names firstLower secondLower
      exact ⟨.act middleName', by simp [Action.rename, Action.lower?, found], by simp [Action.lower?, found']⟩
  | coact name =>
      obtain ⟨middleName, firstLower, rfl⟩ := Option.map_eq_some_iff.mp first
      obtain ⟨outerName, secondLower, rfl⟩ := Option.map_eq_some_iff.mp second
      obtain ⟨middleName', found, found'⟩ := names firstLower secondLower
      exact ⟨.coact middleName', by simp [Action.rename, Action.lower?, found], by simp [Action.lower?, found']⟩
  | tau =>
      simp only [Action.lower?, Option.some.injEq] at first
      subst first
      exact ⟨.tau, rfl, second⟩

theorem Action.rename_swap_swap (action : Action) : (action.rename swapInner).rename swapInner = action := by
  have identity : (fun index => swapInner (swapInner index)) = id := funext swapInner_swapInner
  cases action <;> simp [Action.rename, rename_comp, Function.comp_def, identity, rename_id]

/-- **Exchanging two restrictions matches transitions.** -/
theorem matched_exchange (admitted : admits definitions = true) {free : FreeTypeContext} {bound : List TypeExpr}
    {outerBinder innerBinder : Option String} {body : Pattern}
    (typed : HasType ccsRecCalc free bound
      (.apply "CNu" [.lambda outerBinder (.apply "CNu" [.lambda innerBinder body])]) (.base "Proc"))
    (object : isObjectPattern (.apply "CNu" [.lambda outerBinder (.apply "CNu" [.lambda innerBinder body])]) = true) :
    Matched definitions (.apply "CNu" [.lambda outerBinder (.apply "CNu" [.lambda innerBinder body])])
        (.apply "CNu" [.lambda none (.apply "CNu" [.lambda none (rename swapInner body)])]) ∧
      Matched definitions (.apply "CNu" [.lambda none (.apply "CNu" [.lambda none (rename swapInner body)])])
        (.apply "CNu" [.lambda outerBinder (.apply "CNu" [.lambda innerBinder body])]) := by
  cases restriction_binder (block := ccsBlock) typed
  have innerTyped := restriction_body (block := ccsBlock) typed
  cases restriction_binder (block := ccsBlock) innerTyped
  have bodyTyped := restriction_body (block := ccsBlock) innerTyped
  have bodyObject : isObjectPattern body = true := by
    rw [isObject_restriction, isObject_restriction] at object
    exact object
  constructor
  · intro action target step
    obtain ⟨middle, middleTarget, middleStep, seen, rfl⟩ := lstep_restriction_inv step
    obtain ⟨inner, innerTarget, innerStep, seen', rfl⟩ := lstep_restriction_inv middleStep
    obtain ⟨middle', found, found'⟩ := lower_lower_swap seen' seen
    refine ⟨_, .res none (.res none (innerStep.rename admitted swapInner) found) found', ?_⟩
    have targetTyped := (innerStep.typed admitted bodyTyped bodyObject).1
    exact (exchange_equivalent (block := ccsBlock) targetTyped).toEquationEquiv
  · intro action target step
    obtain ⟨middle, middleTarget, middleStep, seen, rfl⟩ := lstep_restriction_inv step
    obtain ⟨inner, innerTarget, innerStep, seen', rfl⟩ := lstep_restriction_inv middleStep
    obtain ⟨inner₀, innerTarget₀, innerStep₀, rfl, rfl⟩ := innerStep.rename_inv admitted swapInner_injective rfl
    have swapped := lower_lower_swap seen' seen
    rw [Action.rename_swap_swap] at swapped
    obtain ⟨middle', found, found'⟩ := swapped
    refine ⟨_, .res none (.res none innerStep₀ found) found', ?_⟩
    have targetTyped := (innerStep₀.typed admitted bodyTyped bodyObject).1
    exact .symm _ _ (exchange_equivalent (block := ccsBlock) targetTyped).toEquationEquiv

end Mettapedia.Languages.ProcessCalculi.CCS.Recursive
