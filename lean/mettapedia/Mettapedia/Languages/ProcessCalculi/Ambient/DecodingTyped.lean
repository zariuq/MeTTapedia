import Mettapedia.Languages.ProcessCalculi.Ambient.DecodingLaws

/-!
# Read-backs are typed

Reading back keeps variables where they are and every restriction in its place, and both calculi bind the same
sorts, so a typed located block reads back as a typed ambient block in the same context (`decode_typed`): a name
position holding a variable keeps its type, a message keeps its type (`message_typed`), and every ambient constructor
the reading builds takes typed arguments.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Decoding

open Mettapedia.Languages.ProcessCalculi.Ambient.Comm (ambientCoreCalc coreSignature capType)

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (Prenex Members BlockSignature body_typed restricts_typed
  decompose_sound replicate_typed)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (ambientBlock ambientRepBlock amb_typed
  prefix_typed capTerm_typed eps_typed path_typed acap_typed input_typed output_typed)
open Mettapedia.Languages.ProcessCalculi.Ambient.Located (locatedCalc locatedBlock locatedLanguage capabilityRule
  capTermRule inputRule outputRule)
open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (nameType procType)

/-- **A located process of three arguments** is a marker of three names, a capability of two names and a process,
or a prefix by a capability term of a name, a capability term and a process. -/
theorem triple_inv {free : FreeTypeContext} {bound : List TypeExpr} {label : String} {first second third : Pattern}
    (typed : HasType locatedCalc free bound (.apply label [first, second, third]) procType) :
    (label ∈ markers ∧ HasType locatedCalc free bound second nameType ∧ HasType locatedCalc free bound third nameType) ∨
      (label ∈ capabilities ∧ HasType locatedCalc free bound second nameType ∧
        HasType locatedCalc free bound third procType) ∨
      (label = "LCap" ∧ HasType locatedCalc free bound second capType ∧
        HasType locatedCalc free bound third procType) := by
  obtain ⟨rule, member, rfl, notBare, typeIs, arguments⟩ := hasType_apply_inversion typed
  simp only [locatedCalc, capabilityRule, capTermRule, inputRule, outputRule, List.mem_cons,
        List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;>
    simp only [procType, TypeExpr.base.injEq] at typeIs <;> try (exact absurd typeIs (by decide))
  · cases arguments
  · exact absurd ⟨"ps", .hashBag, .base "Proc", rfl⟩ notBare
  · cases arguments with
    | cons _ _ _ rest => cases rest
  · cases arguments with
    | cons _ _ _ rest => cases rest
  all_goals
    cases arguments with
    | cons _ firstParameter firstTyped rest =>
        cases rest with
        | cons _ secondParameter secondTyped rest =>
            first
              | (cases rest; done)
              | cases rest with
                | cons _ thirdParameter thirdTyped last =>
                    cases last
                    simp only [parameterType?, Option.some.injEq] at firstParameter secondParameter thirdParameter
                    subst firstParameter secondParameter thirdParameter
                    first
                      | exact .inl ⟨by simp, secondTyped, thirdTyped⟩
                      | exact .inr (.inl ⟨by simp, secondTyped, thirdTyped⟩)
                      | exact .inr (.inr ⟨rfl, secondTyped, thirdTyped⟩)

/-- **A located process of two arguments** is an input at a name, over a typed body binding a variable of its sort,
or an output at a name of a message of its sort. -/
theorem pair_inv {free : FreeTypeContext} {bound : List TypeExpr} {label : String} {first second : Pattern}
    (typed : HasType locatedCalc free bound (.apply label [first, second]) procType) :
    HasType locatedCalc free bound first nameType ∧
      ((∃ sort body, (label, sort) ∈ [("LInName", "Name"), ("LInCap", "Cap")] ∧ second = .lambda none body ∧
          HasType locatedCalc free (.base sort :: bound) body procType) ∨
        (∃ sort, (label, sort) ∈ [("LOutName", "Name"), ("LOutCap", "Cap")] ∧
          HasType locatedCalc free bound second (.base sort))) := by
  obtain ⟨rule, member, rfl, notBare, typeIs, arguments⟩ := hasType_apply_inversion typed
  simp only [locatedCalc, capabilityRule, capTermRule, inputRule, outputRule, List.mem_cons,
        List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;>
    simp only [procType, TypeExpr.base.injEq] at typeIs <;> try (exact absurd typeIs (by decide))
  · cases arguments
  · exact absurd ⟨"ps", .hashBag, .base "Proc", rfl⟩ notBare
  · cases arguments with
    | cons _ _ _ rest => cases rest
  · cases arguments with
    | cons _ _ _ rest => cases rest
  all_goals
    cases arguments with
    | cons _ firstParameter firstTyped rest =>
        cases rest with
        | cons secondRepresentation secondParameter secondTyped last =>
            first
              | (cases last; done)
              | cases last
                simp only [parameterType?, Option.some.injEq] at firstParameter
                subst firstParameter
                refine ⟨firstTyped, ?_⟩
                first
                  | obtain ⟨body, rfl⟩ :=
                      (matchesParameterRepresentation_abstractionNamed_iff _ _ _ _).mp secondRepresentation
                    simp only [parameterType?, Option.some.injEq] at secondParameter
                    subst secondParameter
                    cases secondTyped with
                    | lambda bodyTyped => exact .inl ⟨_, body, by simp, rfl, bodyTyped⟩
                  | simp only [parameterType?, Option.some.injEq] at secondParameter
                    subst secondParameter
                    exact .inr ⟨_, by simp, secondTyped⟩

/-- A typed located replication replicates a typed process. -/
theorem rep_inv {free : FreeTypeContext} {bound : List TypeExpr} {argument : Pattern}
    (typed : HasType locatedCalc free bound (.apply "LRep" [argument]) procType) :
    HasType locatedCalc free bound argument procType := by
  obtain ⟨rule, member, labelIs, -, -, arguments⟩ := hasType_apply_inversion typed
  simp only [locatedCalc, capabilityRule, capTermRule, inputRule, outputRule, List.mem_cons,
        List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;> simp at labelIs
  cases arguments with
  | cons _ parameterType argumentTyped _ =>
      simp only [parameterType?, Option.some.injEq] at parameterType
      subst parameterType
      exact argumentTyped

/-- **A variable of the name sort has it in either calculus.** -/
theorem variable_typed {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern}
    (typed : HasType locatedCalc free bound pattern nameType) (isVar : isVariable pattern = true) :
    HasType ambientCoreCalc free bound pattern nameType := by
  cases pattern with
  | bvar index =>
      cases typed with
      | bvar found => exact .bvar found
  | fvar name =>
      cases typed with
      | fvar found => exact .fvar found
  | _ => simp [isVariable] at isVar

/-- **A message keeps its type in either calculus**: variables keep theirs, and the capability constructors are
those of the core. -/
theorem message_typed {free : FreeTypeContext} :
    ∀ {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr},
      HasType locatedCalc free bound pattern type → isMessage pattern = true →
      HasType ambientCoreCalc free bound pattern type
  | _, .bvar _, _, typed, _ => by
      cases typed with
      | bvar found => exact .bvar found
  | _, .fvar _, _, typed, _ => by
      cases typed with
      | fvar found => exact .fvar found
  | _, .apply label [], _, typed, isMsg => by
      simp only [isMessage, beq_iff_eq] at isMsg
      subst isMsg
      obtain ⟨rule, member, labelIs, -, rfl, -⟩ := hasType_apply_inversion typed
      simp only [locatedCalc, capabilityRule, capTermRule, inputRule, outputRule, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl <;> simp at labelIs
      exact eps_typed
  | _, .apply label [name], _, typed, isMsg => by
      simp only [isMessage, Bool.and_eq_true, decide_eq_true_eq] at isMsg
      obtain ⟨listed, nameVar⟩ := isMsg
      obtain ⟨rule, member, rfl, -, rfl, argumentsTyped⟩ := hasType_apply_inversion typed
      simp only [locatedCalc, capabilityRule, capTermRule, inputRule, outputRule, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl <;> simp at listed
      all_goals
        cases argumentsTyped with
        | cons _ parameter nameTyped rest =>
            cases rest
            simp only [parameterType?, Option.some.injEq] at parameter
            subst parameter
            exact capTerm_typed (by simp) (variable_typed nameTyped nameVar)
  | _, .apply label [first, second], _, typed, isMsg => by
      simp only [isMessage, Bool.and_eq_true, beq_iff_eq] at isMsg
      obtain ⟨⟨rfl, firstMsg⟩, secondMsg⟩ := isMsg
      obtain ⟨rule, member, labelIs, -, rfl, argumentsTyped⟩ := hasType_apply_inversion typed
      simp only [locatedCalc, capabilityRule, capTermRule, inputRule, outputRule, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl <;> simp at labelIs
      cases argumentsTyped with
      | cons _ firstParameter firstTyped rest =>
          cases rest with
          | cons _ secondParameter secondTyped last =>
              cases last
              simp only [parameterType?, Option.some.injEq] at firstParameter secondParameter
              subst firstParameter secondParameter
              exact path_typed (message_typed firstTyped firstMsg) (message_typed secondTyped secondMsg)
  | _, .apply _ (_ :: _ :: _ :: _), _, _, isMsg => by simp [isMessage] at isMsg
  | _, .lambda _ _, _, _, isMsg => by simp [isMessage] at isMsg
  | _, .multiLambda _ _ _, _, _, isMsg => by simp [isMessage] at isMsg
  | _, .subst _ _, _, _, isMsg => by simp [isMessage] at isMsg
  | _, .collection _ _ _, _, _, isMsg => by simp [isMessage] at isMsg

/-- **A marker's content, read, is a process** when the content is. -/
theorem wrapContent_typed {free : FreeTypeContext} {bound : List TypeExpr} (label : String) {name content : Pattern}
    (nameTyped : HasType ambientCoreCalc free bound name nameType)
    (contentTyped : HasType ambientCoreCalc free bound content procType) :
    HasType ambientCoreCalc free bound (wrapContent label name content) procType := by
  unfold wrapContent
  split_ifs
  · exact amb_typed nameTyped contentTyped
  · exact contentTyped

theorem ambientCapability_mem {label : String} (listed : label ∈ capabilities) :
    ambientCapability label ∈ ["AIn", "AOut", "AOpen"] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl <;> simp [ambientCapability]

/-- **Read-backs of typed located blocks are typed ambient blocks**, in the same context. -/
theorem decode_typed {free : FreeTypeContext} : ∀ (fuel : Nat),
    (∀ {bound : List TypeExpr} (place : Pattern) (form : Prenex),
      Members locatedCalc locatedBlock free (List.replicate form.count nameType ++ bound) form.components →
      Members ambientCoreCalc ambientBlock free (List.replicate (decodeForm fuel place form).count nameType ++ bound)
        (decodeForm fuel place form).components) ∧
    (∀ {bound : List TypeExpr} (place : Pattern) (components : List Pattern),
      Members locatedCalc locatedBlock free bound components →
      Members ambientCoreCalc ambientBlock free bound (readPlaced fuel place components)) ∧
    (∀ {bound : List TypeExpr} (place component : Pattern) (components : List Pattern),
      HasType locatedCalc free bound component procType → Members locatedCalc locatedBlock free bound components →
      HasType ambientCoreCalc free bound (readComponent fuel place component components) procType)
  | 0 => ⟨fun _ _ _ => fun _ member => by simp [decodeForm] at member, fun _ _ _ => fun _ member => by
      simp [readPlaced] at member, fun _ _ _ _ _ => Mettapedia.Languages.ProcessCalculi.Ambient.Comm.coreSignature.unit_typed⟩
  | fuel + 1 => by
      have signature : BlockSignature locatedCalc locatedBlock := locatedLanguage.toBlockSignature
      obtain ⟨formsBelow, placedBelow, componentBelow⟩ := decode_typed (free := free) fuel
      have toPatternTyped : ∀ {bound : List TypeExpr} (place process : Pattern),
          HasType locatedCalc free bound process procType →
          HasType ambientCoreCalc free bound (Prenex.toPattern ambientBlock
            (decodeForm fuel place (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.decompose locatedBlock process)))
            procType := by
        intro bound place process typed
        have members := (decompose_sound (language := locatedCalc) (block := locatedBlock) typed).1
        exact restricts_typed (language := ambientCoreCalc) (block := ambientBlock) _
          (body_typed (formsBelow place _ members))
      refine ⟨fun place form members => ?_, fun place components members => ?_,
        fun place component components typed members => ?_⟩
      · obtain ⟨count, formComponents⟩ := form
        exact placedBelow _ formComponents members
      · rw [readPlaced_succ]
        intro element member
        obtain ⟨original, inFiltered, rfl⟩ := List.mem_map.mp member
        exact componentBelow place original _ (members original (List.mem_filter.mp inFiltered).1)
          (fun other inRest => members other (List.mem_filter.mp inRest).1)
      · cases component with
        | apply label arguments =>
            match arguments, typed with
            | [_, second, third], typed =>
                rcases triple_inv typed with ⟨isMarker, secondTyped, thirdTyped⟩ | ⟨listed, secondTyped, thirdTyped⟩ |
                  ⟨rfl, secondTyped, thirdTyped⟩
                rotate_right
                · rw [readComponent_cap]
                  split_ifs with isMsg
                  · exact acap_typed (message_typed secondTyped isMsg) (toPatternTyped place third thirdTyped)
                  · exact Mettapedia.Languages.ProcessCalculi.Ambient.Comm.coreSignature.unit_typed
                all_goals simp only [readComponent]
                · simp only [if_pos isMarker]
                  split_ifs with isVar
                  · exact wrapContent_typed label (variable_typed thirdTyped isVar)
                      (body_typed (placedBelow second components members))
                  · exact Mettapedia.Languages.ProcessCalculi.Ambient.Comm.coreSignature.unit_typed
                · simp only [if_neg (not_marker_of_capability listed), if_pos listed]
                  split_ifs with isVar
                  · exact prefix_typed (ambientCapability_mem listed) (variable_typed secondTyped isVar)
                      (toPatternTyped place third thirdTyped)
                  · exact Mettapedia.Languages.ProcessCalculi.Ambient.Comm.coreSignature.unit_typed
            | [argument], typed =>
                simp only [readComponent]
                split_ifs with isRep
                · subst isRep
                  exact replicate_typed (block := ambientRepBlock) (toPatternTyped place argument (rep_inv typed))
                · exact Mettapedia.Languages.ProcessCalculi.Ambient.Comm.coreSignature.unit_typed
            | [], _ => exact Mettapedia.Languages.ProcessCalculi.Ambient.Comm.coreSignature.unit_typed
            | [_, second], typed =>
                obtain ⟨-, ⟨sort, body, listed, rfl, bodyTyped⟩ | ⟨sort, listed, messageTyped⟩⟩ := pair_inv typed
                · have isInput : label ∈ inputs := by
                    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at listed
                    rcases listed with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
                  rw [readComponent_input isInput]
                  exact input_typed (ambientInput_listed listed) (toPatternTyped (liftBVars 0 1 place) body bodyTyped)
                · have isOutput : label ∈ outputs := by
                    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at listed
                    rcases listed with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
                  rw [readComponent_output isOutput]
                  split_ifs with isMsg
                  · exact output_typed (ambientOutput_listed listed) (message_typed messageTyped isMsg)
                  · exact Mettapedia.Languages.ProcessCalculi.Ambient.Comm.coreSignature.unit_typed
            | _ :: _ :: _ :: _ :: _, _ => exact Mettapedia.Languages.ProcessCalculi.Ambient.Comm.coreSignature.unit_typed
        | _ => exact Mettapedia.Languages.ProcessCalculi.Ambient.Comm.coreSignature.unit_typed

end Mettapedia.Languages.ProcessCalculi.Ambient.Decoding
