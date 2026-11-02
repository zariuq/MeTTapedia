import Mettapedia.TypeTheory.FiniteConstructorEncoding

/-!
# Field maps on finite constructor data and payloads

Field maps preserve the constructor occurrence and ordered arity. Handlers
are precomposed with those maps, giving a covariant map of payloads. Encoding
commutes with the construction. Field retractions lift to payload retractions
on the represented guarded image, without a countability assumption.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.FiniteConstructorEncoding
open IndexedPolynomial.Description
universe u s
variable {SortCode : Type s} {Source Target Further : SortCode → Type u}

def mapFields (maps : ∀ sort, Source sort → Target sort) :
    (fields : List SortCode) → Env Source fields → Env Target fields
  | [], _ => PUnit.unit
  | _ :: rest, data => (maps _ data.1,mapFields maps rest data.2)

theorem mapFields_id (fields : List SortCode) (data : Env Source fields) :
    mapFields (fun _ value => value) fields data = data := by
  induction fields with
  | nil => cases data; rfl
  | cons sort rest previous => exact congrArg (Prod.mk data.1) (previous data.2)

theorem mapFields_comp (first : ∀ sort, Source sort → Target sort)
    (second : ∀ sort, Target sort → Further sort) (fields : List SortCode) (data : Env Source fields) :
    mapFields second fields (mapFields first fields data) =
      mapFields (fun sort value => second sort (first sort value)) fields data := by
  induction fields with
  | nil => rfl
  | cons sort rest previous => exact congrArg (Prod.mk _) (previous data.2)

def mapData (maps : ∀ sort, Source sort → Target sort)
    (signature : Signature (SortCode := SortCode)) (data : Data Source signature) : Data Target signature :=
  ⟨data.1,mapFields maps (signature.get data.1) data.2⟩

theorem mapData_id (signature : Signature (SortCode := SortCode)) (data : Data Source signature) :
    mapData (fun _ value => value) signature data = data := by
  rcases data with ⟨occurrence,fields⟩
  exact congrArg (Sigma.mk occurrence) (mapFields_id _ fields)

theorem mapData_comp (first : ∀ sort, Source sort → Target sort)
    (second : ∀ sort, Target sort → Further sort)
    (signature : Signature (SortCode := SortCode)) (data : Data Source signature) :
    mapData second signature (mapData first signature data) =
      mapData (fun sort value => second sort (first sort value)) signature data := by
  exact congrArg (Sigma.mk data.1) (mapFields_comp first second _ data.2)

def precomposeHandler (maps : ∀ sort, Source sort → Target sort)
    (fields : List SortCode) (handler : Handler Target fields) : Handler Source fields :=
  curry Source fields (fun data => apply Target fields handler (mapFields maps fields data))

theorem precomposeHandler_apply (maps : ∀ sort, Source sort → Target sort)
    (fields : List SortCode) (handler : Handler Target fields) (data : Env Source fields) :
    apply Source fields (precomposeHandler maps fields handler) data =
      apply Target fields handler (mapFields maps fields data) := apply_curry _ _ _ _

theorem precomposeHandler_id (fields : List SortCode) (handler : Handler Source fields) :
    precomposeHandler (fun _ value => value) fields handler = handler := by
  unfold precomposeHandler
  simp only [mapFields_id]
  exact curry_apply _ _ _

theorem precomposeHandler_comp (first : ∀ sort, Source sort → Target sort)
    (second : ∀ sort, Target sort → Further sort) (fields : List SortCode) (handler : Handler Further fields) :
    precomposeHandler first fields (precomposeHandler second fields handler) =
      precomposeHandler (fun sort value => second sort (first sort value)) fields handler := by
  apply (curryEquivalence Source fields).symm.injective
  funext data
  exact (precomposeHandler_apply first fields _ data).trans
    ((precomposeHandler_apply second fields handler _).trans
      ((congrArg (apply Further fields handler) (mapFields_comp first second fields data)).trans
        (precomposeHandler_apply _ fields handler data).symm))

def precomposeHandlers (maps : ∀ sort, Source sort → Target sort) :
    (signature : Signature (SortCode := SortCode)) → Handlers Target signature → Handlers Source signature
  | [], _ => PUnit.unit
  | fields :: rest, handlers =>
      (precomposeHandler maps fields handlers.1,precomposeHandlers maps rest handlers.2)

theorem precomposeHandlers_id (signature : Signature (SortCode := SortCode)) (handlers : Handlers Source signature) :
    precomposeHandlers (fun _ value => value) signature handlers = handlers := by
  induction signature with
  | nil => cases handlers; rfl
  | cons fields rest previous => exact congrArg₂ Prod.mk (precomposeHandler_id fields handlers.1) (previous handlers.2)

theorem precomposeHandlers_comp (first : ∀ sort, Source sort → Target sort)
    (second : ∀ sort, Target sort → Further sort) (signature : Signature (SortCode := SortCode))
    (handlers : Handlers Further signature) :
    precomposeHandlers first signature (precomposeHandlers second signature handlers) =
      precomposeHandlers (fun sort value => second sort (first sort value)) signature handlers := by
  induction signature with
  | nil => rfl
  | cons fields rest previous =>
      exact congrArg₂ Prod.mk (precomposeHandler_comp first second fields handlers.1) (previous handlers.2)

def mapPayload (maps : ∀ sort, Source sort → Target sort)
    (signature : Signature (SortCode := SortCode)) (payload : Payload Source signature) : Payload Target signature :=
  curry (Handler Target) signature (fun handlers =>
    apply (Handler Source) signature payload (precomposeHandlers maps signature handlers))

theorem mapPayload_apply (maps : ∀ sort, Source sort → Target sort)
    (signature : Signature (SortCode := SortCode)) (payload : Payload Source signature) (handlers : Handlers Target signature) :
    apply (Handler Target) signature (mapPayload maps signature payload) handlers =
      apply (Handler Source) signature payload (precomposeHandlers maps signature handlers) := apply_curry _ _ _ _

theorem mapPayload_id (signature : Signature (SortCode := SortCode)) (payload : Payload Source signature) :
    mapPayload (fun _ value => value) signature payload = payload := by
  unfold mapPayload
  simp only [precomposeHandlers_id]
  exact curry_apply _ _ _

theorem mapPayload_comp (first : ∀ sort, Source sort → Target sort)
    (second : ∀ sort, Target sort → Further sort) (signature : Signature (SortCode := SortCode))
    (payload : Payload Source signature) :
    mapPayload second signature (mapPayload first signature payload) =
      mapPayload (fun sort value => second sort (first sort value)) signature payload := by
  apply (curryEquivalence (Handler Further) signature).symm.injective
  funext handlers
  change apply (Handler Further) signature (mapPayload second signature (mapPayload first signature payload)) handlers =
    apply (Handler Further) signature (mapPayload (fun sort value => second sort (first sort value)) signature payload) handlers
  simp only [mapPayload_apply,precomposeHandlers_comp]

theorem select_precomposeHandlers (maps : ∀ sort, Source sort → Target sort)
    (signature : Signature (SortCode := SortCode)) (occurrence : Fin signature.length)
    (handlers : Handlers Target signature) :
    select Source signature occurrence (precomposeHandlers maps signature handlers) =
      precomposeHandler maps (signature.get occurrence) (select Target signature occurrence handlers) := by
  induction signature with
  | nil => exact Fin.elim0 occurrence
  | cons fields rest previous =>
      rcases occurrence with ⟨n,bound⟩
      cases n with
      | zero => rfl
      | succ n => exact previous ⟨n,Nat.lt_of_succ_lt_succ bound⟩ handlers.2

theorem mapPayload_encode (maps : ∀ sort, Source sort → Target sort)
    (signature : Signature (SortCode := SortCode)) (data : Data Source signature) :
    mapPayload maps signature (encode Source signature data) = encode Target signature (mapData maps signature data) := by
  apply (curryEquivalence (Handler Target) signature).symm.injective
  funext handlers
  change apply (Handler Target) signature (mapPayload maps signature (encode Source signature data)) handlers =
    apply (Handler Target) signature (encode Target signature (mapData maps signature data)) handlers
  simp only [mapPayload_apply,encode,apply_curry,select_precomposeHandlers,precomposeHandler_apply,mapData]

def fieldsValid (guard : ∀ sort, Source sort → Prop) : (fields : List SortCode) → Env Source fields → Prop
  | [], _ => True
  | sort :: rest, data => guard sort data.1 ∧ fieldsValid guard rest data.2

theorem mapFields_roundtrip (lower : ∀ sort, Source sort → Target sort)
    (raise : ∀ sort, Target sort → Source sort) (guard : ∀ sort, Source sort → Prop)
    (recover : ∀ sort value, guard sort value → raise sort (lower sort value) = value)
    (fields : List SortCode) (data : Env Source fields) (valid : fieldsValid guard fields data) :
    mapFields raise fields (mapFields lower fields data) = data := by
  induction fields with
  | nil => cases data; rfl
  | cons sort rest previous => exact congrArg₂ Prod.mk (recover sort data.1 valid.1) (previous data.2 valid.2)

def payloadGuard (guard : ∀ sort, Source sort → Prop) (signature : Signature (SortCode := SortCode))
    (payload : Payload Source signature) : Prop :=
  ∃ data : Data Source signature, fieldsValid guard (signature.get data.1) data.2 ∧ encode Source signature data = payload

theorem mapPayload_roundtrip (lower : ∀ sort, Source sort → Target sort)
    (raise : ∀ sort, Target sort → Source sort) (guard : ∀ sort, Source sort → Prop)
    (recover : ∀ sort value, guard sort value → raise sort (lower sort value) = value)
    (signature : Signature (SortCode := SortCode)) (payload : Payload Source signature)
    (valid : payloadGuard guard signature payload) :
    mapPayload raise signature (mapPayload lower signature payload) = payload := by
  obtain ⟨⟨occurrence,data⟩,valid,rfl⟩ := valid
  rw [mapPayload_encode,mapPayload_encode]
  apply congrArg (encode Source signature)
  exact congrArg (Sigma.mk occurrence) (mapFields_roundtrip lower raise guard recover _ data valid)

theorem mapPayload_injective_on_guard (lower : ∀ sort, Source sort → Target sort)
    (raise : ∀ sort, Target sort → Source sort) (guard : ∀ sort, Source sort → Prop)
    (recover : ∀ sort value, guard sort value → raise sort (lower sort value) = value)
    (signature : Signature (SortCode := SortCode)) (first second : Payload Source signature)
    (firstValid : payloadGuard guard signature first) (secondValid : payloadGuard guard signature second)
    (same : mapPayload lower signature first = mapPayload lower signature second) : first = second := by
  exact (mapPayload_roundtrip lower raise guard recover signature first firstValid).symm.trans
    ((congrArg (mapPayload raise signature) same).trans
      (mapPayload_roundtrip lower raise guard recover signature second secondValid))

#print axioms mapPayload_encode
#print axioms mapPayload_comp
#print axioms mapPayload_injective_on_guard
end Mettapedia.TypeTheory.FiniteConstructorEncoding
