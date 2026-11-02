import Mettapedia.Languages.ProcessCalculi.Ambient.EncodingRename
import Mettapedia.Languages.ProcessCalculi.Ambient.DecodingRename

/-!
# The located form and substitution

Reading a process located with an assignment of terms to its variables (`encodeWith`) generalizes reading it with a
renaming (`encode_eq_encodeWith`). Substituting into a located form is reading the process with the substituted
assignment, at the substituted location (`substitute_encodeWith`); and reading a process whose variables received
messages — names and capability terms — is reading it with the composite assignment (`encodeWith_substitute`). So the
located form of a continuation that received a message is the located continuation with the located message received
(`encode_instantiate`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Encoding

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars instantiateBVar)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (liftIndex)
open Mettapedia.OSLF.MeTTaIL.ContextSubstitution (Assignment substitute lift single substituteList_eq_map lift_comp
  substitute_comp substitute_liftBVars lift_zero substitute_id substitute_single_eq_instantiateBVar)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (rename size sizeList liftBVars_eq_rename shiftAbove)
open Mettapedia.Languages.ProcessCalculi.Ambient.Decoding (isMessage isVariable isMessage_rename)

/-- An assignment read one binder deeper: each image moved past a new innermost variable. -/
def shiftAssign (assign : Assignment) : Assignment := fun index => shiftName (assign index)

mutual
  /-- **The located form of an ambient process with an assignment**: as `encode`, its variables read through the
  assignment rather than renamed. -/
  def encodeWith (assign : Assignment) (here : Pattern) : Pattern → Pattern
    | .apply label [] => if label = "AZero" then .apply "LZero" [] else .apply label []
    | .apply label [.lambda binder body] =>
        if label = "ANu" then .apply "LNu" [.lambda binder (encodeWith (lift 1 assign) (shiftName here) body)]
        else if label = "AInName" then
          .apply "LInName" [here, .lambda binder (encodeWith (lift 1 assign) (shiftName here) body)]
        else if label = "AInCap" then
          .apply "LInCap" [here, .lambda binder (encodeWith (lift 1 assign) (shiftName here) body)]
        else substitute assign (.apply label [.lambda binder body])
    | .apply label [argument] =>
        if label = "ARep" then .apply "LRep" [encodeWith assign here argument]
        else if label = "AOutName" then .apply "LOutName" [here, substitute assign argument]
        else if label = "AOutCap" then .apply "LOutCap" [here, substitute assign argument]
        else substitute assign (.apply label [argument])
    | .apply label [name, process] =>
        if label = "AAmb" then
          .apply "LNu" [.lambda none (.collection .hashBag
            [.apply "LAmb" [shiftName here, .bvar 0, substitute (shiftAssign assign) name],
              encodeWith (shiftAssign assign) (.bvar 0) process] none)]
        else if label = "AIn" then .apply "LIn" [here, substitute assign name, encodeWith assign here process]
        else if label = "AOut" then .apply "LOut" [here, substitute assign name, encodeWith assign here process]
        else if label = "AOpen" then .apply "LOpen" [here, substitute assign name, encodeWith assign here process]
        else if label = "ACap" then .apply "LCap" [here, substitute assign name, encodeWith assign here process]
        else substitute assign (.apply label [name, process])
    | .collection .hashBag elements tail => .collection .hashBag (encodeWithList assign here elements) tail
    | other => substitute assign other

  /-- The located forms of the members of a bag, with an assignment. -/
  def encodeWithList (assign : Assignment) (here : Pattern) : List Pattern → List Pattern
    | [] => []
    | first :: rest => encodeWith assign here first :: encodeWithList assign here rest
end

theorem encodeWithList_eq_map (assign : Assignment) (here : Pattern) :
    ∀ elements : List Pattern, encodeWithList assign here elements = elements.map (encodeWith assign here)
  | [] => rfl
  | first :: rest => by rw [encodeWithList, encodeWithList_eq_map assign here rest, List.map_cons]

theorem encodeWith_single {assign : Assignment} {here : Pattern} (label : String) {argument : Pattern}
    (notLambda : ∀ binder body, argument ≠ .lambda binder body) :
    encodeWith assign here (.apply label [argument]) =
      if label = "ARep" then .apply "LRep" [encodeWith assign here argument]
      else if label = "AOutName" then .apply "LOutName" [here, substitute assign argument]
      else if label = "AOutCap" then .apply "LOutCap" [here, substitute assign argument]
      else substitute assign (.apply label [argument]) := by
  cases argument with
  | lambda binder body => exact absurd rfl (notLambda binder body)
  | _ => simp [encodeWith]

theorem encodeWith_single_lambda (assign : Assignment) (here : Pattern) (label : String) (binder : Option String)
    (body : Pattern) :
    encodeWith assign here (.apply label [.lambda binder body]) =
      if label = "ANu" then .apply "LNu" [.lambda binder (encodeWith (lift 1 assign) (shiftName here) body)]
      else if label = "AInName" then
        .apply "LInName" [here, .lambda binder (encodeWith (lift 1 assign) (shiftName here) body)]
      else if label = "AInCap" then
        .apply "LInCap" [here, .lambda binder (encodeWith (lift 1 assign) (shiftName here) body)]
      else substitute assign (.apply label [.lambda binder body]) := by
  simp [encodeWith]

theorem encodeWith_pair (assign : Assignment) (here : Pattern) (label : String) (name process : Pattern) :
    encodeWith assign here (.apply label [name, process]) =
      if label = "AAmb" then
        .apply "LNu" [.lambda none (.collection .hashBag
          [.apply "LAmb" [shiftName here, .bvar 0, substitute (shiftAssign assign) name],
            encodeWith (shiftAssign assign) (.bvar 0) process] none)]
      else if label = "AIn" then .apply "LIn" [here, substitute assign name, encodeWith assign here process]
      else if label = "AOut" then .apply "LOut" [here, substitute assign name, encodeWith assign here process]
      else if label = "AOpen" then .apply "LOpen" [here, substitute assign name, encodeWith assign here process]
      else if label = "ACap" then .apply "LCap" [here, substitute assign name, encodeWith assign here process]
      else substitute assign (.apply label [name, process]) := by
  simp [encodeWith]

/-! ## Renamings are assignments -/

/-- The assignment of a renaming. -/
abbrev renamingOf (relabel : Nat → Nat) : Assignment := fun index => .bvar (relabel index)

theorem rename_eq_substitute (relabel : Nat → Nat) (pattern : Pattern) :
    rename relabel pattern = substitute (renamingOf relabel) pattern := rfl

theorem lift_renaming_one (relabel : Nat → Nat) : lift 1 (renamingOf relabel) = renamingOf (liftIndex 1 relabel) := by
  funext index
  cases index with
  | zero => simp [lift, liftIndex]
  | succ index => simp [lift, liftIndex, liftBVars]

theorem shiftName_eq_liftBVars (pattern : Pattern) : shiftName pattern = liftBVars 0 1 pattern := by
  rw [liftBVars_eq_rename]
  unfold shiftName
  congr 1

theorem shiftAssign_renaming (relabel : Nat → Nat) : shiftAssign (renamingOf relabel) = renamingOf (Nat.succ ∘ relabel) := by
  funext index
  simp [shiftAssign, shiftName, rename_eq_substitute, substitute]

/-- **Reading located with a renaming is reading with its assignment.** -/
theorem encode_eq_encodeWith : ∀ (fuel : Nat) {pattern : Pattern}, size pattern < fuel →
    ∀ (relabel : Nat → Nat) (here : Pattern), encode relabel here pattern = encodeWith (renamingOf relabel) here pattern
  | 0, _, small, _, _ => absurd small (Nat.not_lt_zero _)
  | fuel + 1, pattern, small, relabel, here => by
      cases pattern with
      | bvar index => simp [encode, encodeWith, rename_eq_substitute]
      | fvar name => simp [encode, encodeWith, rename_eq_substitute]
      | lambda binder body => simp [encode, encodeWith, rename_eq_substitute]
      | multiLambda arity binders body => simp [encode, encodeWith, rename_eq_substitute]
      | subst body replacement => simp [encode, encodeWith, rename_eq_substitute]
      | collection kind elements rest =>
          cases kind with
          | hashBag =>
              simp only [encode, encodeWith, encodeList_eq_map, encodeWithList_eq_map]
              congr 1
              refine List.map_congr_left fun element member => ?_
              exact encode_eq_encodeWith fuel (by have := size_lt_of_mem' member; simp only [size] at small; omega)
                relabel here
          | _ => simp [encode, encodeWith, rename_eq_substitute]
      | apply label arguments =>
          match arguments, small with
          | [], _ => simp [encode, encodeWith]
          | [argument], small =>
              have argumentSmall : size argument < fuel := by simp only [size, sizeList] at small; omega
              by_cases isLambda : ∃ binder body, argument = .lambda binder body
              · obtain ⟨binder, body, rfl⟩ := isLambda
                have bodySmall : size body < fuel := by simp only [size] at argumentSmall; omega
                rw [encode_single_lambda, encodeWith_single_lambda, lift_renaming_one,
                  encode_eq_encodeWith fuel bodySmall]
                rfl
              · push Not at isLambda
                rw [encode_single label isLambda, encodeWith_single label isLambda,
                  encode_eq_encodeWith fuel argumentSmall]
                rfl
          | [name, process], small =>
              have processSmall : size process < fuel := by simp only [size, sizeList] at small; omega
              rw [encode_pair, encodeWith_pair, shiftAssign_renaming, encode_eq_encodeWith fuel processSmall,
                encode_eq_encodeWith fuel processSmall]
              rfl
          | _ :: _ :: _ :: _, _ => simp [encode, encodeWith, rename_eq_substitute]

/-! ## Substituting into a located form -/

theorem substitute_shiftName (assignment : Assignment) (pattern : Pattern) :
    substitute (lift 1 assignment) (shiftName pattern) = shiftName (substitute assignment pattern) := by
  rw [shiftName_eq_liftBVars, shiftName_eq_liftBVars]
  simpa only [Nat.zero_add, lift_zero] using substitute_liftBVars assignment pattern 0 1

theorem substitute_shiftAssign (assign : Assignment) (pattern : Pattern) :
    substitute (shiftAssign assign) pattern = shiftName (substitute assign pattern) := by
  conv_rhs => rw [shiftName, rename_eq_substitute, substitute_comp]
  rfl

theorem lift_one_zero (assignment : Assignment) : lift 1 assignment 0 = .bvar 0 := by
  simp [lift]

theorem encodeWith_lambda (assign : Assignment) (here : Pattern) (binder : Option String) (body : Pattern) :
    encodeWith assign here (.lambda binder body) = substitute assign (.lambda binder body) := by
  simp only [encodeWith]

theorem encodeWith_multiLambda (assign : Assignment) (here : Pattern) (arity : Nat) (binders : List String)
    (body : Pattern) :
    encodeWith assign here (.multiLambda arity binders body) = substitute assign (.multiLambda arity binders body) := by
  simp only [encodeWith]

theorem encodeWith_subst (assign : Assignment) (here body replacement : Pattern) :
    encodeWith assign here (.subst body replacement) = substitute assign (.subst body replacement) := by
  simp only [encodeWith]

theorem encodeWith_collection_other (assign : Assignment) (here : Pattern) {kind : CollType} (notBag : kind ≠ .hashBag)
    (elements : List Pattern) (rest : Option String) :
    encodeWith assign here (.collection kind elements rest) = substitute assign (.collection kind elements rest) := by
  cases kind with
  | hashBag => exact absurd rfl notBag
  | _ => simp only [encodeWith]

theorem encodeWith_many (assign : Assignment) (here : Pattern) (label : String) (first second third : Pattern)
    (rest : List Pattern) :
    encodeWith assign here (.apply label (first :: second :: third :: rest)) =
      substitute assign (.apply label (first :: second :: third :: rest)) := by
  simp only [encodeWith]

/-- **Substituting into a located form is reading the process with the substituted assignment**, at the substituted
location. -/
theorem substitute_encodeWith : ∀ (fuel : Nat) {pattern : Pattern}, size pattern < fuel →
    ∀ (assignment assign : Assignment) (here : Pattern),
      substitute assignment (encodeWith assign here pattern) =
        encodeWith (fun index => substitute assignment (assign index)) (substitute assignment here) pattern
  | 0, _, small, _, _, _ => absurd small (Nat.not_lt_zero _)
  | fuel + 1, pattern, small, assignment, assign, here => by
      cases pattern with
      | bvar index => simp [encodeWith, substitute]
      | fvar name => simp [encodeWith, substitute]
      | lambda binder body => simp only [encodeWith, substitute_comp]
      | multiLambda arity binders body => simp only [encodeWith, substitute_comp]
      | subst body replacement => simp only [encodeWith, substitute_comp]
      | collection kind elements rest =>
          cases kind with
          | hashBag =>
              simp only [encodeWith, encodeWithList_eq_map, substitute, substituteList_eq_map, List.map_map]
              congr 1
              refine List.map_congr_left fun element member => ?_
              exact substitute_encodeWith fuel
                (by have := size_lt_of_mem' member; simp only [size] at small; omega) assignment assign here
          | _ => simp only [encodeWith, substitute_comp]
      | apply label arguments =>
          match arguments, small with
          | [], _ =>
              by_cases zero : label = "AZero"
              · simp [encodeWith, zero, substitute]
              · simp [encodeWith, zero, substitute]
          | [argument], small =>
              have argumentSmall : size argument < fuel := by simp only [size, sizeList] at small; omega
              by_cases isLambda : ∃ binder body, argument = .lambda binder body
              · obtain ⟨binder, body, rfl⟩ := isLambda
                have bodySmall : size body < fuel := by simp only [size] at argumentSmall; omega
                rw [encodeWith_single_lambda, encodeWith_single_lambda]
                have recurse := substitute_encodeWith fuel bodySmall (lift 1 assignment) (lift 1 assign) (shiftName here)
                rw [lift_comp, substitute_shiftName] at recurse
                split_ifs
                · simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil, recurse]
                · simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil, recurse]
                · simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil, recurse]
                · rw [substitute_comp]
              · push Not at isLambda
                rw [encodeWith_single label isLambda, encodeWith_single label isLambda]
                split_ifs
                · simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil,
                    substitute_encodeWith fuel argumentSmall]
                · simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil, substitute_comp]
                · simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil, substitute_comp]
                · rw [substitute_comp]
          | [name, process], small =>
              have processSmall : size process < fuel := by simp only [size, sizeList] at small; omega
              rw [encodeWith_pair, encodeWith_pair]
              have shifted : (fun index => substitute (lift 1 assignment) (shiftAssign assign index)) =
                  shiftAssign (fun index => substitute assignment (assign index)) := by
                funext index
                exact substitute_shiftName assignment (assign index)
              split_ifs
              · simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil]
                rw [substitute_shiftName, lift_one_zero, substitute_comp, shifted,
                  substitute_encodeWith fuel processSmall, shifted]
                simp only [substitute, lift_one_zero]
              all_goals simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil, substitute_comp,
                substitute_encodeWith fuel processSmall]
          | _ :: _ :: _ :: _, _ => simp only [encodeWith, substitute_comp]

/-! ## Reading a process that received messages -/

/-- **A message reads located as its substitution**: names and capability terms have no located structure. -/
theorem encodeWith_message {assign : Assignment} {here message : Pattern} (isMsg : isMessage message = true) :
    encodeWith assign here message = substitute assign message := by
  match message, isMsg with
  | .bvar _, _ => simp [encodeWith]
  | .fvar _, _ => simp [encodeWith]
  | .apply label [name], isMsg =>
      simp only [isMessage, Bool.and_eq_true, decide_eq_true_eq, List.mem_cons, List.not_mem_nil, or_false] at isMsg
      obtain ⟨listed, nameVar⟩ := isMsg
      have notLambda : ∀ binder body, name ≠ .lambda binder body := by
        intro binder body same
        subst same
        simp [isVariable] at nameVar
      rw [encodeWith_single label notLambda]
      rcases listed with rfl | rfl | rfl <;> simp
  | .apply label [], isMsg =>
      simp only [isMessage, beq_iff_eq] at isMsg
      subst isMsg
      simp [encodeWith, substitute]
  | .apply label [first, second], isMsg =>
      simp only [isMessage, Bool.and_eq_true, beq_iff_eq] at isMsg
      obtain ⟨⟨rfl, -⟩, -⟩ := isMsg
      rw [encodeWith_pair]
      simp

theorem message_notLambda {message : Pattern} (isMsg : isMessage message = true) :
    ∀ binder body, message ≠ .lambda binder body := by
  intro binder body same
  subst same
  simp [isMessage] at isMsg

/-- Lifting past a binder keeps an assignment of messages. -/
theorem messages_lift {assignment : Assignment} (messages : ∀ index, isMessage (assignment index) = true) :
    ∀ index, isMessage (lift 1 assignment index) = true := by
  intro index
  cases index with
  | zero => simp [lift, isMessage]
  | succ index =>
      have notBelow : ¬ index + 1 < 1 := by omega
      simp only [lift, notBelow, ite_false, Nat.add_sub_cancel]
      rw [liftBVars_eq_rename, isMessage_rename]
      exact messages index

/-- **Reading a process whose variables received messages is reading it with the composite assignment.** -/
theorem encodeWith_substitute : ∀ (fuel : Nat) {pattern : Pattern}, size pattern < fuel →
    ∀ (assignment assign : Assignment) (here : Pattern), (∀ index, isMessage (assignment index) = true) →
      encodeWith assign here (substitute assignment pattern) =
        encodeWith (fun index => substitute assign (assignment index)) here pattern
  | 0, _, small, _, _, _, _ => absurd small (Nat.not_lt_zero _)
  | fuel + 1, pattern, small, assignment, assign, here, messages => by
      have plain : Mettapedia.GSLT.LanguageDef.RestrictionBlocks.NoAbstractions assignment :=
        fun index => message_notLambda (messages index)
      cases pattern with
      | bvar index => simp [substitute, encodeWith, encodeWith_message (messages index)]
      | fvar name => simp [substitute, encodeWith]
      | lambda binder body =>
          have unfolded : substitute assignment (.lambda binder body) =
              .lambda binder (substitute (lift 1 assignment) body) := by simp only [substitute]
          rw [unfolded, encodeWith_lambda, encodeWith_lambda, ← unfolded, substitute_comp]
      | multiLambda arity binders body =>
          have unfolded : substitute assignment (.multiLambda arity binders body) =
              .multiLambda arity binders (substitute (lift arity assignment) body) := by simp only [substitute]
          rw [unfolded, encodeWith_multiLambda, encodeWith_multiLambda, ← unfolded, substitute_comp]
      | subst body replacement =>
          have unfolded : substitute assignment (.subst body replacement) =
              .subst (substitute (lift 1 assignment) body) (substitute assignment replacement) := by
            simp only [substitute]
          rw [unfolded, encodeWith_subst, encodeWith_subst, ← unfolded, substitute_comp]
      | collection kind elements rest =>
          by_cases bag : kind = .hashBag
          · subst bag
            simp only [substitute, substituteList_eq_map, encodeWith, encodeWithList_eq_map, List.map_map]
            congr 1
            refine List.map_congr_left fun element member => ?_
            exact encodeWith_substitute fuel
              (by have := size_lt_of_mem' member; simp only [size] at small; omega) assignment assign here messages
          · have unfolded : substitute assignment (.collection kind elements rest) =
                .collection kind (elements.map (substitute assignment)) rest := by
              simp only [substitute, substituteList_eq_map]
            rw [unfolded, encodeWith_collection_other _ _ bag, encodeWith_collection_other _ _ bag, ← unfolded,
              substitute_comp]
      | apply label arguments =>
          match arguments, small with
          | [], _ => simp [substitute, encodeWith]
          | [argument], small =>
              have argumentSmall : size argument < fuel := by simp only [size, sizeList] at small; omega
              by_cases isLambda : ∃ binder body, argument = .lambda binder body
              · obtain ⟨binder, body, rfl⟩ := isLambda
                have bodySmall : size body < fuel := by simp only [size] at argumentSmall; omega
                have substituted : substitute assignment (.apply label [.lambda binder body]) =
                    .apply label [.lambda binder (substitute (lift 1 assignment) body)] := by
                  simp [substitute, substituteList_eq_map]
                rw [substituted, encodeWith_single_lambda, encodeWith_single_lambda,
                  encodeWith_substitute fuel bodySmall _ _ _ (messages_lift messages), lift_comp]
                split_ifs
                · rfl
                · rfl
                · rfl
                · rw [← substituted, substitute_comp]
              · push Not at isLambda
                have substitutedNot := Mettapedia.GSLT.LanguageDef.RestrictionBlocks.substitute_notLambda plain isLambda
                have substituted : substitute assignment (.apply label [argument]) =
                    .apply label [substitute assignment argument] := by
                  simp [substitute, substituteList_eq_map]
                rw [substituted, encodeWith_single label substitutedNot, encodeWith_single label isLambda]
                split_ifs
                · rw [encodeWith_substitute fuel argumentSmall _ _ _ messages]
                · rw [substitute_comp]
                · rw [substitute_comp]
                · rw [← substituted, substitute_comp]
          | [name, process], small =>
              have processSmall : size process < fuel := by simp only [size, sizeList] at small; omega
              have substituted : substitute assignment (.apply label [name, process]) =
                  .apply label [substitute assignment name, substitute assignment process] := by
                simp [substitute, substituteList_eq_map]
              have shifted : (fun index => substitute (shiftAssign assign) (assignment index)) =
                  shiftAssign (fun index => substitute assign (assignment index)) := by
                funext index
                exact substitute_shiftAssign assign (assignment index)
              rw [substituted, encodeWith_pair, encodeWith_pair]
              split_ifs
              · rw [substitute_comp, shifted, encodeWith_substitute fuel processSmall _ _ _ messages, shifted]
              all_goals first
                | rw [substitute_comp, encodeWith_substitute fuel processSmall _ _ _ messages]
                | rw [← substituted, substitute_comp]
          | first :: second :: third :: rest, _ =>
              have unfolded : substitute assignment (.apply label (first :: second :: third :: rest)) =
                  .apply label (substitute assignment first :: substitute assignment second ::
                    substitute assignment third :: rest.map (substitute assignment)) := by
                simp only [substitute, substituteList_eq_map, List.map_cons]
              rw [unfolded, encodeWith_many, encodeWith_many, ← unfolded, substitute_comp]

/-! ## Receiving a message -/

/-- Receiving a message for the innermost variable is an assignment of messages. -/
theorem single_messages {message : Pattern} (isMsg : isMessage message = true) :
    ∀ index, isMessage (single message index) = true
  | 0 => isMsg
  | _ + 1 => rfl

/-- **Receiving a term for a variable moved past the innermost binder gives the term back.** -/
theorem substitute_single_shiftName (replacement pattern : Pattern) :
    substitute (single replacement) (shiftName pattern) = pattern := by
  rw [shiftName, rename_eq_substitute, substitute_comp]
  exact substitute_id pattern

/-- **The located form of a continuation that received a message is the located continuation with the located message
received.** -/
theorem encode_instantiate {relabel : Nat → Nat} {here message body : Pattern} (isMsg : isMessage message = true) :
    instantiateBVar (rename relabel message) (encode (liftIndex 1 relabel) (shiftName here) body) =
      encode relabel here (instantiateBVar message body) := by
  rw [← substitute_single_eq_instantiateBVar, ← substitute_single_eq_instantiateBVar,
    encode_eq_encodeWith (size body + 1) (Nat.lt_succ_self _),
    encode_eq_encodeWith (size (substitute (single message) body) + 1) (Nat.lt_succ_self _),
    substitute_encodeWith (size body + 1) (Nat.lt_succ_self _),
    encodeWith_substitute (size body + 1) (Nat.lt_succ_self _) _ _ _ (single_messages isMsg),
    substitute_single_shiftName]
  congr 1
  funext index
  cases index with
  | zero => simp [single, liftIndex, rename_eq_substitute, substitute]
  | succ index => simp [single, renamingOf, liftIndex, substitute]

end Mettapedia.Languages.ProcessCalculi.Ambient.Encoding
