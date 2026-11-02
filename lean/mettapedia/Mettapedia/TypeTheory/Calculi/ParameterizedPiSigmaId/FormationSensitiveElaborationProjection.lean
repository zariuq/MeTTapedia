import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveElaboration

/-!
# Type and success observations of the existing elaboration producer

These functions retain the original source, contexts, choices, ordering and
fuel. They omit typing-code fields while observing inferred types and success.
The internal unit value records presence only; it supplies no certificate.
Publication still requires the original independent replay of the original
produced code. Neither producer success nor its projection establishes typing.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.FormationSensitiveElaboration

variable {Head : Type} {RootCode : Nat → Type}
  (R : Rules Head) (choices : Choices Head RootCode) [DecidableEq Head]

mutual

def typeProjection : Nat → {n : Nat} → Ctx Head n → Tm Head n → Option (Tm Head n)
  | 0, _, _, _ => none
  | fuel+1, _, context, term => match term with
    | .var index => some (Ctx.lookup context index)
    | .head head => do return .head (← choices.headType head)
    | .const name => do
        let type ← R.constantType name
        let formation ← typeProjection fuel .nil type
        match formation with
        | .head _ => return liftClosed type
        | _ => none
    | .pi domain body => do
        let first ← typeProjection fuel context domain
        let second ← typeProjection fuel (.snoc context domain) body
        match first,second with
        | .head u,.head v => do return .head (← choices.join u v)
        | _,_ => none
    | .sigma domain body => do
        let first ← typeProjection fuel context domain
        let second ← typeProjection fuel (.snoc context domain) body
        match first,second with
        | .head u,.head v => do return .head (← choices.join u v)
        | _,_ => none
    | .id carrier left right => do
        let formation ← typeProjection fuel context carrier
        match formation with
        | .head level => do
            let _ ← checkPresence fuel context left carrier
            let _ ← checkPresence fuel context right carrier
            return .head level
        | _ => none
    | .refl subject => do
        let type ← typeProjection fuel context subject
        return .id type subject subject
    | .app (.lam body) argument => do
        let argumentType ← typeProjection fuel context argument
        let bodyType ← typeProjection fuel (.snoc context argumentType) body
        let formation ← typeProjection fuel context (.pi argumentType bodyType)
        match formation with
        | .head _ => return inst0 argument bodyType
        | _ => none
    | .app function argument => do
        let inferred ← typeProjection fuel context function
        let viewed := choices.normalize fuel inferred
        match viewed with
        | .pi domain body => do
            let _ ← alignPresence fuel context function inferred viewed
            let _ ← checkPresence fuel context argument domain
            return inst0 argument body
        | _ => none
    | .fst pair => do
        let inferred ← typeProjection fuel context pair
        let viewed := choices.normalize fuel inferred
        match viewed with
        | .sigma domain _ => do
            let _ ← alignPresence fuel context pair inferred viewed
            return domain
        | _ => none
    | .snd pair => do
        let inferred ← typeProjection fuel context pair
        let viewed := choices.normalize fuel inferred
        match viewed with
        | .sigma _ body => do
            let _ ← alignPresence fuel context pair inferred viewed
            return inst0 (.fst pair) body
        | _ => none
    | .lam _ | .pair _ _ => none

def checkPresence : Nat → {n : Nat} → Ctx Head n → Tm Head n → Tm Head n → Option Unit
  | 0, _, _, _, _ => none
  | fuel+1, _, context, term, expected =>
      let viewed := choices.normalize fuel expected
      match term,viewed with
      | .lam body,.pi domain codomain => do
          let formation ← typeProjection fuel context viewed
          match formation with
          | .head _ => do
              let _ ← checkPresence fuel (.snoc context domain) body codomain
              alignPresence fuel context term viewed expected
          | _ => none
      | .pair first second,.sigma domain codomain => do
          let formation ← typeProjection fuel context viewed
          match formation with
          | .head _ => do
              let _ ← checkPresence fuel context first domain
              let _ ← checkPresence fuel context second (inst0 first codomain)
              alignPresence fuel context term viewed expected
          | _ => none
      | .refl subject,.id carrier _ _ => do
          let _ ← checkPresence fuel context subject carrier
          alignPresence fuel context term (.id carrier subject subject) expected
      | _,_ => do
          let inferred ← typeProjection fuel context term
          alignPresence fuel context term inferred expected

def alignPresence : Nat → {n : Nat} → Ctx Head n → Tm Head n → Tm Head n → Tm Head n → Option Unit
  | 0, _, _, _, _, _ => none
  | fuel+1, _, context, _term, source, target =>
      if source = target then some () else
        let cumulative := match source,target with
          | .head first,.head second => choices.cumulative first second
          | _,_ => false
        if cumulative then some () else do
          let formation ← typeProjection fuel context target
          match formation with
          | .head _ => do
              let _ ← choices.conversion fuel source target
              return ()
          | _ => none

end

def checkProjection (fuel : Nat) {n : Nat} (context : Ctx Head n) (term type : Tm Head n) : Bool :=
  (checkPresence R choices fuel context term type).isSome

def alignProjection (fuel : Nat) {n : Nat} (context : Ctx Head n)
    (term source target : Tm Head n) : Bool :=
  (alignPresence R choices fuel context term source target).isSome

private theorem bind_discard {α β : Type} (value : Option α) (observed : Option Unit)
    (same : value.map (fun _ => ()) = observed) (next : Option β) :
    value.bind (fun _ => next) = observed.bind (fun _ => next) := by
  rw [← same]
  cases value <;> rfl

private theorem producer_projections (fuel : Nat) :
    (∀ {n : Nat} (context : Ctx Head n) (term : Tm Head n),
      (synth R choices fuel context term).map Inferred.type = typeProjection R choices fuel context term) ∧
    (∀ {n : Nat} (context : Ctx Head n) (term type : Tm Head n),
      (check R choices fuel context term type).map (fun _ => ()) = checkPresence R choices fuel context term type) ∧
    (∀ {n : Nat} (context : Ctx Head n) (term source target : Tm Head n) (evidence : Code Head RootCode n),
      (align R choices fuel context term source target evidence).map (fun _ => ()) =
        alignPresence R choices fuel context term source target) := by
  induction fuel with
  | zero => exact ⟨fun _ _ => rfl,fun _ _ _ => rfl,fun _ _ _ _ _ => rfl⟩
  | succ fuel ih =>
      have alignBind {n : Nat} (context : Ctx Head n) (term source target : Tm Head n)
          (evidence : Code Head RootCode n) {β : Type} (next : Option β) :
          (align R choices fuel context term source target evidence).bind (fun _ => next) =
            (alignPresence R choices fuel context term source target).bind (fun _ => next) :=
        bind_discard _ _ (ih.2.2 context term source target evidence) next
      refine ⟨?_,?_,?_⟩
      · intro n context term
        cases term <;>
          simp only [synth,typeProjection,Option.bind_eq_bind,Option.pure_def,Option.map_bind,Option.bind_map,Option.map_some,Option.map_none,
            Function.comp_def,← ih.1,← ih.2.1]
        all_goals
          repeat' first
            | rfl
            | (apply Option.bind_congr; intro value found)
            | (split <;> simp only [*,Option.map_bind,
                Option.map_some,Option.map_none,Function.comp_def])
      · intro n context term type
        cases term <;>
          simp only [check,checkPresence,Option.bind_eq_bind,Option.map_bind,Option.bind_map,
            Function.comp_def,← ih.1,← ih.2.1,ih.2.2]
        all_goals
          repeat' first
            | rfl
            | (apply Option.bind_congr; intro value found)
            | (split <;> simp only [*,Option.map_bind,
                Option.map_none,Function.comp_def,ih.2.2])
      · intro n context term source target evidence
        by_cases same : source = target
        · simp only [align,alignPresence,same,if_true,Option.pure_def,Option.map_some]
        · cases source <;> cases target <;>
            simp only [align,alignPresence,same,if_false,Option.bind_eq_bind,Option.pure_def,Option.map_bind,
              Option.bind_map,Function.comp_def,← ih.1,Bool.false_eq_true]
          all_goals
            try (split_ifs <;> simp only [*,Option.map_bind,
              Option.map_some,Function.comp_def])
          all_goals
            repeat' first
              | rfl
              | (apply Option.bind_congr; intro value found)
              | (split <;> simp only [*,Option.map_bind,
                  Option.map_some,Option.map_none,Function.comp_def])

theorem synth_type (fuel : Nat) {n : Nat} (context : Ctx Head n) (term : Tm Head n) :
    (synth R choices fuel context term).map Inferred.type = typeProjection R choices fuel context term :=
  (producer_projections R choices fuel).1 context term

theorem check_success (fuel : Nat) {n : Nat} (context : Ctx Head n) (term type : Tm Head n) :
    (check R choices fuel context term type).isSome = checkProjection R choices fuel context term type := by
  rw [checkProjection,← (producer_projections R choices fuel).2.1 context term type,Option.isSome_map]

theorem align_success (fuel : Nat) {n : Nat} (context : Ctx Head n)
    (term source target : Tm Head n) (evidence : Code Head RootCode n) :
    (align R choices fuel context term source target evidence).isSome =
      alignProjection R choices fuel context term source target := by
  rw [alignProjection,← (producer_projections R choices fuel).2.2 context term source target evidence,
    Option.isSome_map]

#print axioms synth_type
#print axioms check_success
#print axioms align_success

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.FormationSensitiveElaboration
