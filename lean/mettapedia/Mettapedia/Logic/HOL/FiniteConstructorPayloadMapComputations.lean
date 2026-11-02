import Mettapedia.Logic.HOL.FiniteConstructorPayloadMaps

/-!
# Retained computations of finite constructor payload maps

Constant handler continuations remain constant under the actual payload map.
These proofs use explicit beta steps and lambda congruence, without an inverse
claim on the surrounding function space.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.FiniteConstructorEncoding
open FiniteConstructorFieldProjection
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
  {Δ : List (Formula Const Γ)}

def applyArguments_both_congr (fields : List (Ty Base))
    (first second : Term Const Γ (handlerType fields))
    (firstArguments secondArguments : Arguments Const Γ fields)
    (functions : ProofSyntax Const Δ (.eq first second))
    (arguments : ∀ {type : Ty Base} (index : Var fields type),
      ProofSyntax Const Δ (.eq (argumentAt index firstArguments) (argumentAt index secondArguments))) :
    ProofSyntax Const Δ (.eq (applyArguments fields first firstArguments) (applyArguments fields second secondArguments)) := by
  induction fields with
  | nil => exact functions
  | cons type rest previous =>
      exact previous (.app first firstArguments.1) (.app second secondArguments.1) firstArguments.2 secondArguments.2
        (.eqTrans (.eqApp firstArguments.1 functions) (.eqAppArg second (arguments .vz)))
        (fun index => arguments (.vs index))

theorem applyArguments_both_congr_free (fields : List (Ty Base))
    (first second : Term Const Γ (handlerType fields))
    (firstArguments secondArguments : Arguments Const Γ fields)
    (functions : ProofSyntax Const Δ (.eq first second))
    (arguments : ∀ {type : Ty Base} (index : Var fields type),
      ProofSyntax Const Δ (.eq (argumentAt index firstArguments) (argumentAt index secondArguments)))
    (functionsFree : functions.FunctionExtensionalityFree)
    (argumentsFree : ∀ {type : Ty Base} (index : Var fields type), (arguments index).FunctionExtensionalityFree) :
    (applyArguments_both_congr fields first second firstArguments secondArguments functions arguments).FunctionExtensionalityFree := by
  induction fields with
  | nil => exact functionsFree
  | cons type rest previous =>
      exact previous _ _ _ _ _ _ ⟨functionsFree,argumentsFree .vz⟩ (fun index => argumentsFree (.vs index))

def weaken_field_equalities {fields : List (Ty Base)} {bound : Ty Base}
    (first second : Arguments Const Γ fields)
    (same : ∀ {type : Ty Base} (index : Var fields type),
      ProofSyntax Const Δ (.eq (argumentAt index first) (argumentAt index second)))
    {type : Ty Base} (index : Var fields type) :
    ProofSyntax Const (weakenHyps (σ := bound) Δ)
      (.eq (argumentAt index (weakenArguments bound fields first)) (argumentAt index (weakenArguments bound fields second))) := by
  apply ProofSyntax.castIndices rfl ?_ ((same index).rename Rename.weaken)
  simp only [HOL.rename,argumentAt_weaken,HOL.weaken]

theorem weaken_field_equalities_free {fields : List (Ty Base)} {bound : Ty Base}
    (first second : Arguments Const Γ fields)
    (same : ∀ {type : Ty Base} (index : Var fields type),
      ProofSyntax Const Δ (.eq (argumentAt index first) (argumentAt index second)))
    (free : ∀ {type : Ty Base} (index : Var fields type), (same index).FunctionExtensionalityFree)
    {type : Ty Base} (index : Var fields type) :
    (weaken_field_equalities (bound := bound) first second same index).FunctionExtensionalityFree := by
  unfold weaken_field_equalities
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    ((ProofSyntax.functionExtensionalityFree_rename _ _).mpr (free index))

def ignoreHandlers_congr : {Γ : Ctx Base} → {Δ : List (Formula Const Γ)} →
    (signature : List (List (Ty Base))) → (first second : Formula Const Γ) →
    ProofSyntax Const Δ (.eq first second) →
    ProofSyntax Const Δ (.eq (ignoreHandlers signature first) (ignoreHandlers signature second))
  | _,_,[],_,_,same => same
  | _,_,_ :: rest,_,_,same => .eqLam (ignoreHandlers_congr rest _ _ (same.rename Rename.weaken))

theorem ignoreHandlers_congr_free (signature : List (List (Ty Base))) (first second : Formula Const Γ)
    (same : ProofSyntax Const Δ (.eq first second)) (free : same.FunctionExtensionalityFree) :
    (ignoreHandlers_congr signature first second same).FunctionExtensionalityFree := by
  induction signature generalizing Γ with
  | nil => exact free
  | cons fields rest previous =>
      exact previous _ _ _ ((ProofSyntax.functionExtensionalityFree_rename _ _).mpr free)

def encode_congr : {Γ : Ctx Base} → {Δ : List (Formula Const Γ)} →
    (signature : List (List (Ty Base))) → (occurrence : Fin signature.length) →
    (first second : Arguments Const Γ (signature.get occurrence)) →
    (∀ {type : Ty Base} (index : Var (signature.get occurrence) type),
      ProofSyntax Const Δ (.eq (argumentAt index first) (argumentAt index second))) →
    ProofSyntax Const Δ (.eq (encode signature occurrence first) (encode signature occurrence second))
  | _,_,[],occurrence,_,_,_ => Fin.elim0 occurrence
  | _,_,fields :: rest,⟨0,_⟩,first,second,same =>
      .eqLam (ignoreHandlers_congr rest _ _
        (applyArguments_both_congr fields (.var .vz) (.var .vz)
          (weakenArguments _ fields first) (weakenArguments _ fields second) (.eqRefl (.var .vz))
          (weaken_field_equalities first second same)))
  | _,_,fields :: rest,⟨index + 1,bound⟩,first,second,same =>
      .eqLam (encode_congr rest ⟨index,Nat.lt_of_succ_lt_succ bound⟩
        (weakenArguments (handlerType fields) _ first) (weakenArguments (handlerType fields) _ second)
        (weaken_field_equalities first second same))

theorem encode_congr_free (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (first second : Arguments Const Γ (signature.get occurrence))
    (same : ∀ {type : Ty Base} (index : Var (signature.get occurrence) type),
      ProofSyntax Const Δ (.eq (argumentAt index first) (argumentAt index second)))
    (free : ∀ {type : Ty Base} (index : Var (signature.get occurrence) type), (same index).FunctionExtensionalityFree) :
    (encode_congr signature occurrence first second same).FunctionExtensionalityFree := by
  induction signature generalizing Γ with
  | nil => exact Fin.elim0 occurrence
  | cons fields rest previous =>
      rcases occurrence with ⟨index,bound⟩
      cases index with
      | zero =>
          apply ignoreHandlers_congr_free
          apply applyArguments_both_congr_free
          · trivial
          · exact weaken_field_equalities_free _ _ _ free
      | succ index => exact previous _ _ _ _ (weaken_field_equalities_free _ _ _ free)

theorem ignoreHandlers_weaken {type : Ty Base} (signature : List (List (Ty Base))) (body : Formula Const Γ) :
    weaken (σ := type) (ignoreHandlers signature body) = ignoreHandlers signature (weaken body) := by
  simpa only [subst_ofRename,HOL.weaken] using
    ignoreHandlers_subst (Subst.ofRename (Rename.weaken (σ := type))) signature body

def ignoreHead_beta (fields : List (Ty Base)) (rest : List (List (Ty Base)))
    (body : Formula Const Γ) (handler : Term Const Γ (handlerType fields)) :
    ProofSyntax Const Δ (.eq (.app (ignoreHandlers (fields :: rest) body) handler) (ignoreHandlers rest body)) := by
  apply ProofSyntax.castIndices rfl ?_ (.beta handler (ignoreHandlers rest (weaken body)))
  simp only [instantiate,ignoreHandlers_subst,PredicateFixedPoint.subst_single_weaken]
  rfl

theorem ignoreHead_beta_free (fields : List (Ty Base)) (rest : List (List (Ty Base)))
    (body : Formula Const Γ) (handler : Term Const Γ (handlerType fields)) :
    (ignoreHead_beta (Δ := Δ) fields rest body handler).FunctionExtensionalityFree := by
  unfold ignoreHead_beta
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr True.intro

def encode_head_beta (fields : List (Ty Base)) (rest : List (List (Ty Base)))
    (arguments : Arguments Const Γ fields) (handler : Term Const Γ (handlerType fields)) :
    ProofSyntax Const Δ (.eq (.app (encode (fields :: rest) ⟨0,Nat.zero_lt_succ _⟩ arguments) handler)
      (ignoreHandlers rest (applyArguments fields handler arguments))) := by
  apply ProofSyntax.castIndices rfl ?_
    (.beta handler (ignoreHandlers rest (applyArguments fields (.var .vz) (weakenArguments (handlerType fields) fields arguments))))
  simp [encode,instantiate,ignoreHandlers_subst,applyArguments_subst,HOL.subst,Subst.single,substituteArguments_single]

theorem encode_head_beta_free (fields : List (Ty Base)) (rest : List (List (Ty Base)))
    (arguments : Arguments Const Γ fields) (handler : Term Const Γ (handlerType fields)) :
    (encode_head_beta (Δ := Δ) fields rest arguments handler).FunctionExtensionalityFree := by
  unfold encode_head_beta
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr True.intro

def encode_tail_beta (fields : List (Ty Base)) (rest : List (List (Ty Base)))
    (index : Fin rest.length) (arguments : Arguments Const Γ (rest.get index))
    (handler : Term Const Γ (handlerType fields)) :
    ProofSyntax Const Δ (.eq (.app (encode (fields :: rest) ⟨index.val + 1,Nat.succ_lt_succ index.isLt⟩ arguments) handler)
      (encode rest index arguments)) := by
  apply ProofSyntax.castIndices rfl ?_
    (.beta handler (encode rest index (weakenArguments (handlerType fields) _ arguments)))
  simp [encode,instantiate,encode_subst,substituteArguments_single]

theorem encode_tail_beta_free (fields : List (Ty Base)) (rest : List (List (Ty Base)))
    (index : Fin rest.length) (arguments : Arguments Const Γ (rest.get index))
    (handler : Term Const Γ (handlerType fields)) :
    (encode_tail_beta (Δ := Δ) fields rest index arguments handler).FunctionExtensionalityFree := by
  unfold encode_tail_beta
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr True.intro

namespace InventoryMaps
variable {source target : List (List (Ty Base))}

def mapPayload_ignoreHandlers : {Γ : Ctx Base} → {Δ : List (Formula Const Γ)} →
    {source target : List (List (Ty Base))} → (maps : InventoryMaps Const Γ source target) →
    (body : Formula Const Γ) →
    ProofSyntax Const Δ (.eq (maps.mapPayload (ignoreHandlers source body)) (ignoreHandlers target body))
  | _,_,_,_,.nil,body =>
      ProofSyntax.castIndices rfl (by simp only [mapPayload,ignoreHandlers]) (.eqRefl body)
  | _context,assumptions,_,_,@InventoryMaps.cons _ _ _ fields _ rest _ current remaining,body => by
      let handler := (current.subst (Subst.ofRename Rename.weaken)).precompose (.var .vz)
      have selected : ProofSyntax Const (weakenHyps assumptions)
          (.eq (.app (weaken (ignoreHandlers (fields :: rest) body)) handler) (ignoreHandlers rest (weaken body))) := by
        apply ProofSyntax.castIndices rfl ?_ (ignoreHead_beta fields rest (weaken body) handler)
        rw [ignoreHandlers_weaken]
      apply ProofSyntax.castIndices rfl ?_
        (.eqLam (.eqTrans ((remaining.subst (Subst.ofRename Rename.weaken)).mapPayload_congr _ _ selected)
          (mapPayload_ignoreHandlers (remaining.subst (Subst.ofRename Rename.weaken)) (weaken body))))
      simp only [mapPayload,ignoreHandlers,handler]
termination_by _ _ source _ _ _ => source.length

theorem mapPayload_ignoreHandlers_free (maps : InventoryMaps Const Γ source target) (body : Formula Const Γ) :
    (maps.mapPayload_ignoreHandlers (Δ := Δ) body).FunctionExtensionalityFree := by
  induction source generalizing Γ target with
  | nil =>
      cases maps
      simp only [mapPayload_ignoreHandlers,ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.FunctionExtensionalityFree]
  | cons fields rest previous =>
      cases maps with
      | cons current remaining =>
          simp only [mapPayload_ignoreHandlers,ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.FunctionExtensionalityFree]
          constructor
          · apply mapPayload_congr_free
            exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr (ignoreHead_beta_free _ _ _ _)
          · exact previous _ _

def mapPayload_encode : {Γ : Ctx Base} → {Δ : List (Formula Const Γ)} →
    {source target : List (List (Ty Base))} → (maps : InventoryMaps Const Γ source target) →
    (index : Fin source.length) → (arguments : Arguments Const Γ (source.get index)) →
    ProofSyntax Const Δ (.eq (maps.mapPayload (encode source index arguments))
      (encode target (maps.occurrence index) ((maps.row index).apply arguments)))
  | _,_,_,_,.nil,index,_ => Fin.elim0 index
  | _context,assumptions,_,_,@InventoryMaps.cons _ _ _ fields targetFields rest targets current remaining,⟨0,_⟩,arguments => by
      let shiftedCurrent := current.subst (Subst.ofRename (Rename.weaken (σ := handlerType targetFields)))
      let shiftedRemaining := remaining.subst (Subst.ofRename (Rename.weaken (σ := handlerType targetFields)))
      let data := weakenArguments (handlerType targetFields) fields arguments
      let handler := shiftedCurrent.precompose (.var .vz)
      have selected : ProofSyntax Const (weakenHyps assumptions)
          (.eq (.app (weaken (encode (fields :: rest) ⟨0,Nat.zero_lt_succ _⟩ arguments)) handler)
            (ignoreHandlers rest (applyArguments fields handler data))) := by
        apply ProofSyntax.castIndices rfl ?_ (encode_head_beta fields rest data handler)
        rw [weaken_encode]
        rfl
      have fieldComputation : ProofSyntax Const (weakenHyps assumptions)
          (.eq (applyArguments fields handler data)
            (applyArguments targetFields (.var .vz) (weakenArguments (handlerType targetFields) targetFields (current.apply arguments)))) := by
        apply ProofSyntax.castIndices rfl ?_ (shiftedCurrent.precompose_at (.var .vz) data)
        rw [FieldMaps.apply_weaken]
      have computed := ProofSyntax.eqTrans (shiftedRemaining.mapPayload_congr _ _ selected)
        (.eqTrans (shiftedRemaining.mapPayload_ignoreHandlers (applyArguments fields handler data))
          (ignoreHandlers_congr targets _ _ fieldComputation))
      apply ProofSyntax.castIndices rfl ?_ (.eqLam computed)
      simp only [mapPayload,encode,occurrence,row,shiftedCurrent,shiftedRemaining,handler]
  | _context,assumptions,_,_,@InventoryMaps.cons _ _ _ fields targetFields rest targets current remaining,⟨index + 1,bound⟩,arguments => by
      let prior : Fin rest.length := ⟨index,Nat.lt_of_succ_lt_succ bound⟩
      let shiftedCurrent := current.subst (Subst.ofRename (Rename.weaken (σ := handlerType targetFields)))
      let shiftedRemaining := remaining.subst (Subst.ofRename (Rename.weaken (σ := handlerType targetFields)))
      let data := weakenArguments (handlerType targetFields) (rest.get prior) arguments
      let handler := shiftedCurrent.precompose (.var .vz)
      have skipped : ProofSyntax Const (weakenHyps assumptions)
          (.eq (.app (weaken (encode (fields :: rest) ⟨index + 1,bound⟩ arguments)) handler)
            (encode rest prior data)) := by
        apply ProofSyntax.castIndices rfl ?_ (encode_tail_beta fields rest prior data handler)
        rw [weaken_encode]
        rfl
      have computed := ProofSyntax.eqTrans (shiftedRemaining.mapPayload_congr _ _ skipped)
        (mapPayload_encode shiftedRemaining prior data)
      apply ProofSyntax.castIndices rfl ?_ (.eqLam computed)
      simp only [mapPayload,encode,occurrence,row,shiftedCurrent,shiftedRemaining,handler,data,row_subst,FieldMaps.apply_weaken]
      rfl
termination_by _ _ source _ _ _ _ => source.length

theorem mapPayload_encode_free (maps : InventoryMaps Const Γ source target) (index : Fin source.length)
    (arguments : Arguments Const Γ (source.get index)) :
    (maps.mapPayload_encode (Δ := Δ) index arguments).FunctionExtensionalityFree := by
  induction source generalizing Γ target with
  | nil => cases maps; exact Fin.elim0 index
  | cons fields rest previous =>
      cases maps with
      | cons current remaining =>
          rcases index with ⟨index,bound⟩
          cases index with
          | zero =>
              simp only [mapPayload_encode,ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.FunctionExtensionalityFree]
              refine ⟨?_,mapPayload_ignoreHandlers_free _ _,?_⟩
              · apply mapPayload_congr_free
                exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr (encode_head_beta_free _ _ _ _)
              · apply ignoreHandlers_congr_free
                exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr (FieldMaps.precompose_at_free _ _ _)
          | succ index =>
              simp only [mapPayload_encode,ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.FunctionExtensionalityFree]
              constructor
              · apply mapPayload_congr_free
                exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr (encode_tail_beta_free _ _ _ _ _)
              · exact previous _ _ _

#print axioms encode_congr
#print axioms encode_congr_free
#print axioms mapPayload_ignoreHandlers
#print axioms mapPayload_ignoreHandlers_free
#print axioms mapPayload_encode
#print axioms mapPayload_encode_free
end InventoryMaps
end Mettapedia.Logic.HOL.FiniteConstructorEncoding
