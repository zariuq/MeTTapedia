import Mettapedia.Logic.HOL.TermInterpretationLaws
import Mettapedia.Logic.HOL.FiniteConstructorGuardProofs

/-!
# Typed field vectors under closed-term interpretation

The complete ordered field vector is translated without choosing an inverse
of the type map. Handler application commutes with interpretation, with the
necessary result-type transport retained explicitly.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.FiniteConstructorEncoding
universe u v u' v'
variable {Base : Type u} {Const : Ty Base → Type v}
  {Target : Type u'} {Symbols : Ty Target → Type v'}
  (interpretation : TermInterpretation Base Const Target Symbols)
  {Γ : Ctx Base}

private def retype {Γ : Ctx Target} {first second : Ty Target} (same : first = second)
    (term : Term Symbols Γ first) : Term Symbols Γ second := same ▸ term

private theorem retype_app {Γ : Ctx Target} {domain first second : Ty Target}
    (same : first = second) (function : Term Symbols Γ (domain ⇒ first))
    (argument : Term Symbols Γ domain) :
    retype same (.app function argument) =
      .app (retype (congrArg (Ty.arr domain) same) function) argument := by
  cases same
  rfl

theorem handlerType_interpret (fields : List (Ty Base)) :
    Ty.substitute interpretation.types (handlerType fields) =
      handlerType (fields.map (Ty.substitute interpretation.types)) := by
  induction fields with
  | nil => rfl
  | cons first rest previous => simp only [handlerType, Ty.substitute_arr, List.map_cons, previous]

theorem payloadType_interpret (signature : List (List (Ty Base))) :
    Ty.substitute interpretation.types (payloadType signature) =
      payloadType (signature.map (List.map (Ty.substitute interpretation.types))) := by
  induction signature with
  | nil => rfl
  | cons first rest previous =>
      simp only [payloadType, Ty.substitute_arr, List.map_cons, handlerType_interpret, previous]

def interpretArguments : (fields : List (Ty Base)) → Arguments Const Γ fields →
    Arguments Symbols (Γ.map (Ty.substitute interpretation.types)) (fields.map (Ty.substitute interpretation.types))
  | [], _ => PUnit.unit
  | _ :: rest, arguments => (interpretation.term arguments.1, interpretArguments rest arguments.2)

def interpretHandler (fields : List (Ty Base)) (handler : Term Const Γ (handlerType fields)) :
    Term Symbols (Γ.map (Ty.substitute interpretation.types))
      (handlerType (fields.map (Ty.substitute interpretation.types))) :=
  retype (handlerType_interpret interpretation fields) (interpretation.term handler)

def interpretPayload (signature : List (List (Ty Base))) (payload : Term Const Γ (payloadType signature)) :
    Term Symbols (Γ.map (Ty.substitute interpretation.types))
      (payloadType (signature.map (List.map (Ty.substitute interpretation.types)))) :=
  retype (payloadType_interpret interpretation signature) (interpretation.term payload)

theorem interpretHandler_heq (fields : List (Ty Base))
    (term : Term Const Γ (handlerType fields)) :
    HEq (interpretHandler interpretation fields term) (interpretation.term term) := by
  unfold interpretHandler
  exact eqRec_heq _ _

theorem applyArguments_heq {Γ : Ctx Target} {fields other : List (Ty Target)}
    (same : fields = other)
    (first : Term Symbols Γ (handlerType fields)) (second : Term Symbols Γ (handlerType other))
    (functions : HEq first second)
    (arguments : Arguments Symbols Γ fields) :
    applyArguments fields first arguments = applyArguments other second (same ▸ arguments) := by
  cases same
  exact congrArg (fun function => applyArguments fields function arguments) (eq_of_heq functions)

theorem interpretArguments_weaken (domain : Ty Base) (fields : List (Ty Base))
    (arguments : Arguments Const Γ fields) :
    interpretArguments interpretation fields (weakenArguments domain fields arguments) =
      weakenArguments (Ty.substitute interpretation.types domain)
        (fields.map (Ty.substitute interpretation.types)) (interpretArguments interpretation fields arguments) := by
  induction fields with
  | nil => rfl
  | cons first rest previous =>
      simp only [interpretArguments, weakenArguments, TermInterpretation.term_weaken]
      exact congrArg (Prod.mk _) (previous arguments.2)

theorem applyArguments_interpret (fields : List (Ty Base))
    (handler : Term Const Γ (handlerType fields)) (arguments : Arguments Const Γ fields) :
    interpretation.term (applyArguments fields handler arguments) =
      applyArguments (fields.map (Ty.substitute interpretation.types))
        (interpretHandler interpretation fields handler) (interpretArguments interpretation fields arguments) := by
  induction fields with
  | nil => rfl
  | cons first rest previous =>
      simp only [applyArguments, interpretArguments]
      rw [previous]
      unfold interpretHandler
      apply congrArg (fun function => applyArguments (rest.map (Ty.substitute interpretation.types)) function
        (interpretArguments interpretation rest arguments.2))
      exact retype_app (handlerType_interpret interpretation rest) (interpretation.term handler)
        (interpretation.term arguments.1)

private theorem ignoreHandlers_weaken_heq {Γ : Ctx Target} {first second : Ty Target}
    (same : first = second) (signature : List (List (Ty Target))) (body : Formula Symbols Γ) :
    HEq (ignoreHandlers signature (weaken (σ := first) body))
      (ignoreHandlers signature (weaken (σ := second) body)) := by
  cases same
  rfl

theorem ignoreHandlers_interpret (signature : List (List (Ty Base))) (body : Formula Const Γ) :
    HEq (interpretation.term (ignoreHandlers signature body))
      (ignoreHandlers (signature.map (List.map (Ty.substitute interpretation.types))) (interpretation.term body)) := by
  induction signature generalizing Γ with
  | nil => rfl
  | cons fields rest previous =>
      simp only [ignoreHandlers, TermInterpretation.term_lam]
      congr 1
      · exact handlerType_interpret interpretation fields
      · exact payloadType_interpret interpretation rest
      · have step := previous (Γ := handlerType fields :: Γ) (weaken (σ := handlerType fields) body)
        have translated : HEq (interpretation.term (ignoreHandlers rest (weaken (σ := handlerType fields) body)))
            (ignoreHandlers (rest.map (List.map (Ty.substitute interpretation.types)))
              (weaken (σ := Ty.substitute interpretation.types (handlerType fields)) (interpretation.term body))) := by
          simpa only [TermInterpretation.term_weaken] using step
        exact translated.trans (ignoreHandlers_weaken_heq (handlerType_interpret interpretation fields) _ _)

def mapOccurrence (signature : List (List (Ty Base))) (occurrence : Fin signature.length) :
    Fin (signature.map (List.map (Ty.substitute interpretation.types))).length :=
  ⟨occurrence.val, by simpa only [List.length_map] using occurrence.isLt⟩

theorem selectedFields_interpret (signature : List (List (Ty Base))) (occurrence : Fin signature.length) :
    (signature.get occurrence).map (Ty.substitute interpretation.types) =
      (signature.map (List.map (Ty.substitute interpretation.types))).get
        (mapOccurrence interpretation signature occurrence) := by
  simp only [List.get_eq_getElem, List.getElem_map, mapOccurrence]

def interpretSelectedArguments (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (arguments : Arguments Const Γ (signature.get occurrence)) :
    Arguments Symbols (Γ.map (Ty.substitute interpretation.types))
      ((signature.map (List.map (Ty.substitute interpretation.types))).get
        (mapOccurrence interpretation signature occurrence)) :=
  selectedFields_interpret interpretation signature occurrence ▸
    interpretArguments interpretation _ arguments

private theorem weakenArguments_retype {Γ : Ctx Target} (domain : Ty Target)
    {fields other : List (Ty Target)} (same : fields = other)
    (arguments : Arguments Symbols Γ fields) :
    (same ▸ weakenArguments domain fields arguments) =
      weakenArguments domain other (same ▸ arguments) := by
  cases same
  rfl

theorem interpretSelectedArguments_weaken (domain : Ty Base)
    (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (arguments : Arguments Const Γ (signature.get occurrence)) :
    interpretSelectedArguments interpretation signature occurrence
      (weakenArguments domain _ arguments) =
      weakenArguments (Ty.substitute interpretation.types domain) _
        (interpretSelectedArguments interpretation signature occurrence arguments) := by
  simp only [interpretSelectedArguments, interpretArguments_weaken, weakenArguments_retype]

private theorem ignoreHandlers_apply_head_heq {Γ : Ctx Target}
    (rest : List (List (Ty Target))) (fields : List (Ty Target)) {domain : Ty Target}
    (same : domain = handlerType fields) (arguments : Arguments Symbols Γ fields) :
    HEq (ignoreHandlers rest (applyArguments fields (retype same (.var .vz))
      (weakenArguments domain fields arguments)))
      (ignoreHandlers rest (applyArguments fields (.var .vz)
        (weakenArguments (handlerType fields) fields arguments))) := by
  cases same
  rfl

private theorem encode_weaken_heq {Γ : Ctx Target} {first second : Ty Target}
    (same : first = second) (signature : List (List (Ty Target)))
    (occurrence : Fin signature.length) (arguments : Arguments Symbols Γ (signature.get occurrence)) :
    HEq (encode signature occurrence (weakenArguments first _ arguments))
      (encode signature occurrence (weakenArguments second _ arguments)) := by
  cases same
  rfl

theorem encode_interpret (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (arguments : Arguments Const Γ (signature.get occurrence)) :
    HEq (interpretation.term (encode signature occurrence arguments))
      (encode (signature.map (List.map (Ty.substitute interpretation.types)))
        (mapOccurrence interpretation signature occurrence)
        (interpretSelectedArguments interpretation signature occurrence arguments)) := by
  induction signature generalizing Γ with
  | nil => exact Fin.elim0 occurrence
  | cons fields rest previous =>
      rcases occurrence with ⟨n, bound⟩
      cases n with
      | zero =>
          simp only [encode, mapOccurrence, interpretSelectedArguments,
            TermInterpretation.term_lam]
          congr 1
          · exact handlerType_interpret interpretation fields
          · exact payloadType_interpret interpretation rest
          · have step := ignoreHandlers_interpret interpretation rest
              (applyArguments fields (.var .vz) (weakenArguments (handlerType fields) fields arguments))
            simp only [applyArguments_interpret, interpretArguments_weaken, interpretHandler,
              TermInterpretation.term_var, Var.mapTypes] at step
            have translated := step.trans (ignoreHandlers_apply_head_heq
              (rest.map (List.map (Ty.substitute interpretation.types)))
              (fields.map (Ty.substitute interpretation.types))
              (handlerType_interpret interpretation fields) (interpretArguments interpretation fields arguments))
            exact translated
      | succ n =>
          simp only [encode, mapOccurrence, interpretSelectedArguments,
            TermInterpretation.term_lam]
          congr 1
          · exact handlerType_interpret interpretation fields
          · exact payloadType_interpret interpretation rest
          · have step := previous ⟨n, Nat.lt_of_succ_lt_succ bound⟩
              (weakenArguments (handlerType fields) _ arguments)
            have translated : HEq (interpretation.term (encode rest ⟨n, Nat.lt_of_succ_lt_succ bound⟩
                (weakenArguments (handlerType fields) _ arguments)))
                (encode (rest.map (List.map (Ty.substitute interpretation.types)))
                  (mapOccurrence interpretation rest ⟨n, Nat.lt_of_succ_lt_succ bound⟩)
                  (weakenArguments (Ty.substitute interpretation.types (handlerType fields)) _
                    (interpretSelectedArguments interpretation rest ⟨n, Nat.lt_of_succ_lt_succ bound⟩ arguments))) := by
              simpa only [interpretSelectedArguments_weaken] using step
            exact translated.trans (encode_weaken_heq (handlerType_interpret interpretation fields) _ _ _)

theorem abstractArguments_interpret (fields : List (Ty Base))
    (body : ArgumentBody Const Γ fields)
    (targetBody : ArgumentBody Symbols (Γ.map (Ty.substitute interpretation.types))
      (fields.map (Ty.substitute interpretation.types)))
    (compatibleBody : ∀ {Δ : Ctx Base} (rho : Subst Const Γ Δ)
      (mapped : Subst Symbols (Γ.map (Ty.substitute interpretation.types))
        (Δ.map (Ty.substitute interpretation.types))),
      (∀ {type} (index : Var Γ type), interpretation.term (rho index) =
        mapped (index.mapTypes interpretation.types)) →
      ∀ arguments, interpretation.term (body rho arguments) =
        targetBody mapped (interpretArguments interpretation fields arguments)) :
    HEq (interpretation.term (abstractArguments fields body))
      (abstractArguments (fields.map (Ty.substitute interpretation.types)) targetBody) := by
  induction fields generalizing Γ with
  | nil =>
      exact heq_of_eq (compatibleBody (fun index => .var index) (fun index => .var index)
        (fun _ => rfl) PUnit.unit)
  | cons first rest previous =>
      simp only [abstractArguments, TermInterpretation.term_lam]
      congr 1
      · exact handlerType_interpret interpretation rest
      · apply previous
        intro Δ rho mapped compatible arguments
        change interpretation.term (body (fun index => rho (.vs index)) (rho .vz, arguments)) =
          targetBody (fun index => mapped (.vs index))
            (mapped .vz, interpretArguments interpretation rest arguments)
        rw [compatibleBody (fun index => rho (.vs index))
          (fun index => mapped (.vs index)) (fun index => compatible (.vs index))]
        exact congrArg (fun head => targetBody (fun index => mapped (.vs index))
          (head, interpretArguments interpretation rest arguments)) (compatible .vz)

private theorem retype_weaken {Γ : Ctx Target} {first second domain : Ty Target}
    (same : first = second) (term : Term Symbols Γ first) :
    retype same (weaken (σ := domain) term) = weaken (retype same term) := by
  cases same
  rfl

theorem existsArguments_interpret (fields : List (Ty Base))
    (predicate : Term Const Γ (handlerType fields)) :
    interpretation.term (existsArguments fields predicate) =
      existsArguments (fields.map (Ty.substitute interpretation.types))
        (interpretHandler interpretation fields predicate) := by
  induction fields generalizing Γ with
  | nil => rfl
  | cons first rest previous =>
      simp only [existsArguments, TermInterpretation.term_ex]
      apply congrArg Term.ex
      rw [previous]
      apply congrArg (existsArguments (rest.map (Ty.substitute interpretation.types)))
      simp only [interpretHandler, TermInterpretation.term_app, TermInterpretation.term_weaken,
        TermInterpretation.term_var, Var.mapTypes]
      rw [retype_app, retype_weaken]

theorem existsArguments_heq {Γ : Ctx Target} {fields other : List (Ty Target)}
    (same : fields = other)
    (first : Term Symbols Γ (handlerType fields)) (second : Term Symbols Γ (handlerType other))
    (functions : HEq first second) :
    existsArguments fields first = existsArguments other second := by
  cases same
  exact congrArg (existsArguments fields) (eq_of_heq functions)

#print axioms applyArguments_interpret
#print axioms interpretArguments_weaken
#print axioms encode_interpret
#print axioms abstractArguments_interpret
#print axioms existsArguments_interpret
end Mettapedia.Logic.HOL.FiniteConstructorEncoding
