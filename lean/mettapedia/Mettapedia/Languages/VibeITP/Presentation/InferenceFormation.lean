import Mettapedia.Languages.VibeITP.Presentation.InferenceProgram

/-!
# Exact authored term and statement formation

Symbol lookup, arity checks, strict bound-variable/literal guards and all
argument checks execute through the shared equation engine. The correspondence
is against the independent kernel's formation computation, not a supplied
certificate that assumes its desired conclusion.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalInference

open ComputationalData ComputationalShift ComputationalSubstitution ComputationalInstantiation
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => inferenceProgram
local notation "A" => inferenceEquations
local notation "H" => computationalHost

private theorem lookup_applies (table : SignatureTable) (symbol : Spec.SymId) :
    Applies P H "vibe:lookup-symbol" [encodeTable table, encodeSymbol symbol]
      (encodeInfoResult (signatureOf table symbol)) := by
  apply reuse_instantiation_call (by decide +kernel)
  apply reuse_substitution_call (by decide +kernel)
  apply (Applies.append_iff shiftProgram substitutionEquations H substitutionEquations_disjoint
    "vibe:lookup-symbol" (by decide +kernel) _ _).mpr
  exact lookup_computes table symbol

private theorem depth_applies (table : SignatureTable) (term : Spec.Term) :
    Applies P H "vibe:depth" [encodeTable table, encode term] (natural (Spec.depth (signatureOf table) term)) :=
  reuse_instantiation_call (by decide +kernel)
    (reuse_substitution_call (by decide +kernel) (depth_computes_in_substitution table term))

private theorem length_applies (items : List Term) :
    Applies P H "vibe:list-length" [.list items] (natural items.length) :=
  reuse_instantiation_call (by decide +kernel)
    (reuse_substitution_call (by decide +kernel) (listLength_computes items))

private theorem view_applies (items : List Term) :
    Applies P H "nik:list-view" [.list items] (listView items) :=
  reuse_instantiation_call (by decide +kernel)
    (.primitive (by rfl) (computationalHost_list_view items))

private theorem add_applies (left right : Nat) :
    Applies P H "nik:nat-add" [natural left, natural right] (natural (left + right)) :=
  reuse_instantiation_call (by decide +kernel)
    (.primitive (by rfl) (naturalArithmeticHost_add left right))

private theorem lt_applies (left right : Nat) :
    Applies P H "nik:nat-lt" [natural left, natural right] (boolean (decide (left < right))) :=
  reuse_instantiation_call (by decide +kernel)
    (.primitive (by rfl) (naturalArithmeticHost_lt left right))

private theorem eq_applies (left right : Nat) :
    Applies P H "nik:nat-eq" [natural left, natural right] (boolean (decide (left = right))) :=
  reuse_instantiation_call (by decide +kernel)
    (.primitive (by rfl) (naturalArithmeticHost_eq left right))

private theorem zero_applies (value : Nat) :
    Applies P H "nik:nat-zero" [natural value] (boolean (decide (value = 0))) := by
  apply reuse_instantiation_call (by decide +kernel)
  apply Applies.primitive (by rfl)
  by_cases zero : value = 0 <;> simpa [zero, boolean] using computationalHost_zero value

private theorem natural_evaluates (environment : Env) (value : Nat) :
    Evaluates P H environment (natural value) (natural value) :=
  (natural_passive P H value).evaluates environment

private theorem encoded_length (arguments : List Spec.Term) : (encodeTerms arguments).length = arguments.length := by
  induction arguments with
  | nil => rfl
  | cons first rest ih => simp only [encodeTerms, List.length_cons, ih]

private theorem formed_app_start (table : SignatureTable) (symbol : Spec.SymId) (arguments : List Spec.Term)
    (result : Bool)
    (next : Applies P H "vibe:formed-info"
      [encodeInfoResult (signatureOf table symbol), encodeTable table, .list (encodeTerms arguments)]
      (boolean result)) :
    Applies P H "vibe:well-formed" [encodeTable table, encode (.app symbol arguments)] (boolean result) := by
  refine inference_equation (equation := A[20])
    (environment := [("table", encodeTable table), ("symbol", encodeSymbol symbol),
      ("arguments", .list (encodeTerms arguments))]) (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) next
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (lookup_applies table symbol)

private theorem formed_info (table : SignatureTable) (info : Spec.SymInfo) (arguments : List Spec.Term)
    (result : Bool)
    (next : Applies P H "vibe:formed-arity" [boolean (decide (arguments.length = info.arity)),
      encodeTable table, .list (encodeTerms arguments)] (boolean result)) :
    Applies P H "vibe:formed-info" [encodeInfoResult (some info), encodeTable table,
      .list (encodeTerms arguments)] (boolean result) := by
  refine inference_equation (equation := A[22])
    (environment := [("kind", encodeKind info.kind), ("binders", encodeBinders info.binders),
      ("table", encodeTable table), ("arguments", .list (encodeTerms arguments))]) (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (values := [boolean (decide (arguments.length = info.arity)),
      encodeTable table, .list (encodeTerms arguments)]) (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) next
  refine Evaluates.call (values := [natural arguments.length, natural info.arity]) (by simp [Special])
    (.cons ?_ (.cons ?_ .nil)) (eq_applies _ _)
  · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
      (by simpa only [encoded_length] using length_applies (encodeTerms arguments))
  · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
      (by simpa only [List.length_map, Spec.SymInfo.arity, encodeBinders] using length_applies (info.binders.map natural))

private theorem formed_arity (fits rest : Bool) (table : SignatureTable) (arguments : List Spec.Term)
    (next : Applies P H "vibe:well-formed-args" [encodeTable table, .list (encodeTerms arguments)] (boolean rest)) :
    Applies P H "vibe:formed-arity" [boolean fits, encodeTable table, .list (encodeTerms arguments)]
      (boolean (fits && rest)) := by
  cases fits with
  | false => exact ⟨1, by rw [inference_apply _ (by decide +kernel)]; rfl⟩
  | true =>
      refine inference_equation (equation := A[24])
        (environment := [("table", encodeTable table), ("arguments", .list (encodeTerms arguments))])
        (by decide +kernel) (by rfl) (by rfl) ?_
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) next

private theorem formed_args_start (table : SignatureTable) (arguments : List Spec.Term) (result : Bool)
    (next : Applies P H "vibe:formed-view" [encodeTable table, listView (encodeTerms arguments)] (boolean result)) :
    Applies P H "vibe:well-formed-args" [encodeTable table, .list (encodeTerms arguments)] (boolean result) := by
  refine inference_equation (equation := A[25])
    (environment := [("table", encodeTable table), ("arguments", .list (encodeTerms arguments))])
    (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons ?_ .nil)) next
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (view_applies _)

private theorem formed_first (first rest : Bool) (table : SignatureTable) (arguments : List Spec.Term)
    (next : Applies P H "vibe:well-formed-args" [encodeTable table, .list (encodeTerms arguments)] (boolean rest)) :
    Applies P H "vibe:formed-first" [boolean first, encodeTable table, .list (encodeTerms arguments)]
      (boolean (first && rest)) := by
  cases first with
  | false => exact ⟨1, by rw [inference_apply _ (by decide +kernel)]; rfl⟩
  | true =>
      refine inference_equation (equation := A[29])
        (environment := [("table", encodeTable table), ("rest", .list (encodeTerms arguments))])
        (by decide +kernel) (by rfl) (by rfl) ?_
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) next

mutual

theorem wellFormed_computes (table : SignatureTable) (term : Spec.Term) :
    Applies P H "vibe:well-formed" [encodeTable table, encode term]
      (boolean (Spec.WellFormed (signatureOf table) term)) := by
  cases term with
  | bvar index =>
      refine inference_equation (equation := A[18])
        (environment := [("table", encodeTable table), ("index", natural index)]) (by decide +kernel) (by rfl) (by rfl) ?_
      refine Evaluates.call (values := [natural (index + 1), natural Spec.wordBound]) (by simp [Special])
        (.cons ?_ (.cons (natural_evaluates _ _) .nil)) (lt_applies _ _)
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (natural_evaluates _ _) .nil)) (add_applies _ _)
  | lit bytes =>
      refine inference_equation (equation := A[19])
        (environment := [("table", encodeTable table), ("bytes", .list (bytes.map encodeByte))])
        (by decide +kernel) (by rfl) (by rfl) ?_
      refine Evaluates.call (values := [natural (bytes.length + 8), natural Spec.wordBound]) (by simp [Special])
        (.cons ?_ (.cons (natural_evaluates _ _) .nil)) (lt_applies _ _)
      refine Evaluates.call (values := [natural bytes.length, natural 8]) (by simp [Special])
        (.cons ?_ (.cons (natural_evaluates _ _) .nil)) (add_applies _ _)
      exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
        (by simpa only [List.length_map] using length_applies (bytes.map encodeByte))
  | app symbol arguments =>
      apply formed_app_start
      cases found : signatureOf table symbol with
      | none => simp only [Spec.WellFormed, found]; exact ⟨1, by rw [inference_apply _ (by decide +kernel)]; rfl⟩
      | some info =>
          simp only [Spec.WellFormed, found]
          apply formed_info
          exact formed_arity (decide (arguments.length = info.arity))
            (Spec.WellFormedList (signatureOf table) arguments) table arguments
            (wellFormedList_computes table arguments)

theorem wellFormedList_computes (table : SignatureTable) (arguments : List Spec.Term) :
    Applies P H "vibe:well-formed-args" [encodeTable table, .list (encodeTerms arguments)]
      (boolean (Spec.WellFormedList (signatureOf table) arguments)) := by
  apply formed_args_start
  cases arguments with
  | nil => exact ⟨1, by rw [inference_apply _ (by decide +kernel)]; rfl⟩
  | cons first rest =>
      refine inference_equation (equation := A[27])
        (environment := [("table", encodeTable table), ("first", encode first),
          ("rest", .list (encodeTerms rest))]) (by decide +kernel) (by rfl) (by rfl) ?_
      refine Evaluates.call (values := [boolean (Spec.WellFormed (signatureOf table) first),
          encodeTable table, .list (encodeTerms rest)]) (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) ?_
      · exact Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (wellFormed_computes table first)
      · exact formed_first _ _ table rest (wellFormedList_computes table rest)

end

theorem formation_result_exact (table : SignatureTable) (term : Spec.Term) (result : Term) :
    Applies P H "vibe:well-formed" [encodeTable table, encode term] result ↔
      result = boolean (Spec.WellFormed (signatureOf table) term) := by
  constructor
  · intro computed
    exact computed.deterministic (wellFormed_computes table term)
  · intro same
    subst result
    exact wellFormed_computes table term

theorem formation_accepts_iff (table : SignatureTable) (term : Spec.Term) :
    Applies P H "vibe:well-formed" [encodeTable table, encode term] (.sym "True") ↔
      Spec.WellFormed (signatureOf table) term = true := by
  rw [formation_result_exact]
  cases Spec.WellFormed (signatureOf table) term <;> simp [boolean]

theorem formation_refuses_iff (table : SignatureTable) (term : Spec.Term) :
    Applies P H "vibe:well-formed" [encodeTable table, encode term] (.sym "False") ↔
      Spec.WellFormed (signatureOf table) term = false := by
  rw [formation_result_exact]
  cases Spec.WellFormed (signatureOf table) term <;> simp [boolean]

private theorem formed_statement_value (formed : Bool) (table : SignatureTable) (term : Spec.Term) :
    Applies P H "vibe:formed-statement-value" [boolean formed, encodeTable table, encode term]
      (boolean (formed && decide (Spec.depth (signatureOf table) term = 0))) := by
  cases formed with
  | false => exact ⟨1, by rw [inference_apply _ (by decide +kernel)]; rfl⟩
  | true =>
      refine inference_equation (equation := A[43])
        (environment := [("table", encodeTable table), ("statement", encode term)]) (by decide +kernel) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special]) (.cons ?_ .nil) (zero_applies _)
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (depth_applies table term)

theorem statementFormation_computes (table : SignatureTable) (term : Spec.Term) :
    Applies P H "vibe:formed-statement" [encodeTable table, encode term]
      (boolean (Spec.WellFormed (signatureOf table) term && decide (Spec.depth (signatureOf table) term = 0))) := by
  refine inference_equation (equation := A[41])
    (environment := [("table", encodeTable table), ("statement", encode term)]) (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))
    (formed_statement_value _ table term)
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (wellFormed_computes table term)

theorem statementFormation_accepts_iff (table : SignatureTable) (term : Spec.Term) :
    Applies P H "vibe:formed-statement" [encodeTable table, encode term] (.sym "True") ↔
      Spec.WellFormed (signatureOf table) term = true ∧ Spec.depth (signatureOf table) term = 0 := by
  constructor
  · intro checked
    have same := checked.deterministic (statementFormation_computes table term)
    cases formed : Spec.WellFormed (signatureOf table) term with
    | false => simp [formed, boolean] at same
    | true =>
        refine ⟨rfl, ?_⟩
        by_contra openTerm
        simp [formed, openTerm, boolean] at same
  · rintro ⟨formed, closed⟩
    simpa only [formed, closed, decide_true, Bool.true_and, boolean, ↓reduceIte] using statementFormation_computes table term

mutual

theorem wellFormed_on_heads (source target : Spec.Sig) (term : Spec.Term)
    (agree : InfoAgree source target (termHeads term)) :
    Spec.WellFormed source term = Spec.WellFormed target term := by
  cases term with
  | bvar _ => rfl
  | lit _ => rfl
  | app symbol arguments =>
      rw [Spec.WellFormed, Spec.WellFormed, agree.head]
      cases found : target symbol with
      | none => rfl
      | some info => rw [wellFormedList_on_heads source target arguments agree.tail]

theorem wellFormedList_on_heads (source target : Spec.Sig) (arguments : List Spec.Term)
    (agree : InfoAgree source target (termHeadsList arguments)) :
    Spec.WellFormedList source arguments = Spec.WellFormedList target arguments := by
  cases arguments with
  | nil => rfl
  | cons first rest =>
      rw [Spec.WellFormedList, Spec.WellFormedList, wellFormed_on_heads source target first agree.left,
        wellFormedList_on_heads source target rest agree.right]

end

theorem formation_computes_for_signature (signature : Spec.Sig) (term : Spec.Term) :
    Applies P H "vibe:well-formed" [encodeTable (tableFor signature (termHeads term)), encode term]
      (boolean (Spec.WellFormed signature term)) := by
  have agree : InfoAgree (signatureOf (tableFor signature (termHeads term))) signature (termHeads term) := by
    intro symbol used
    rw [tableFor_lookup signature _ symbol, if_pos used]
  rw [← wellFormed_on_heads _ _ term agree]
  exact wellFormed_computes _ term

end Mettapedia.Languages.VibeITP.Presentation.ComputationalInference
