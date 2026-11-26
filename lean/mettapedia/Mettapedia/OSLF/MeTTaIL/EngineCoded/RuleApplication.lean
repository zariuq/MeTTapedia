import Mettapedia.OSLF.MeTTaIL.EngineCoded.Matching
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
import Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

/-!
# Rule application computed on codes

A rule's right-hand side receives its bindings shifted from the depth at which
the left-hand side captured each value to the depth at which it is used
(`applyBindingsScoped`). The capture depth of a name (`captureDepth`), the
splicing of a collection's rest (`restSplice`) and this substitution are
computable on codes. Without reflective data a rule matches by the structural
matcher and substitutes scope-correctly, so matching a rule and building its
reduct are computable on codes too.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.EngineCoded

open Mettapedia.Computability
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.PatternCode
open Mettapedia.OSLF.MeTTaIL.PatternCode.CodeComputable'
open CodeComputable

/-! ## Capture depth -/

theorem captureDepthList_eq (name : String) (depth : ℕ) : ∀ patterns : List Pattern,
    captureDepthList name depth patterns = (patterns.map (captureDepth name depth)).findSome? id
  | [] => rfl
  | pattern :: patterns => by
      rw [captureDepthList, captureDepthList_eq name depth patterns]
      cases found : captureDepth name depth pattern <;> simp [found]

/-- The parts of a pattern with the depth below each, for a fixed name. -/
def captureCalls (parameter : String × ℕ) (pattern : Pattern) : List ((String × ℕ) × Pattern) :=
  (underCalls (· + ·) parameter.2 pattern).map fun call => ((parameter.1, call.1), call.2)

/-- The capture depth at a node, from those of its parts. -/
def captureCombine (parameter : String × ℕ) (pattern : Pattern) (values : List (Option ℕ)) : Option ℕ :=
  @Pattern.casesOn (fun _ => Option ℕ) pattern (fun _ => none)
    (fun other => if other == parameter.1 then some parameter.2 else none)
    (fun _ _ => values.findSome? id) (fun _ _ => values.findSome? id) (fun _ _ _ => values.findSome? id)
    (fun _ _ => values.findSome? id)
    (fun _ _ rest => Option.casesOn (motive := fun _ => Option ℕ) (values.findSome? id)
      (Option.casesOn (motive := fun _ => Option ℕ) rest none
        fun restName => if restName == parameter.1 then some parameter.2 else none)
      some)

theorem capture_node (parameter : String × ℕ) (pattern : Pattern) :
    captureDepth parameter.1 parameter.2 pattern = captureCombine parameter pattern
      ((captureCalls parameter pattern).map fun call => captureDepth call.1.1 call.1.2 call.2) := by
  obtain ⟨name, depth⟩ := parameter
  cases pattern with
  | subst body replacement =>
      simp only [captureDepth, captureCombine, captureCalls, underCalls, partBinders, parts]
      cases found : captureDepth name (depth + 1) body <;> simp [found]
  | collection kind elements rest =>
      have values : (captureCalls (name, depth) (.collection kind elements rest)).map
          (fun call => captureDepth call.1.1 call.1.2 call.2) = elements.map (captureDepth name depth) := by
        simp [captureCalls, underCalls, partBinders, parts, zip_zeros, Function.comp_def]
      rw [values]
      simp only [captureDepth, captureCombine, captureDepthList_eq]
      cases (elements.map (captureDepth name depth)).findSome? id <;> cases rest <;> rfl
  | apply label arguments =>
      simp [captureDepth, captureCombine, captureCalls, underCalls, partBinders, parts, captureDepthList_eq,
        zip_zeros, Function.comp_def]
  | _ => simp [captureDepth, captureCombine, captureCalls, underCalls, partBinders, parts]

theorem captureCalls_computable : CodeComputable₂ captureCalls :=
  list_map ((underCalls_codeComputable Primrec.nat_add.to_comp).comp (pair (snd.comp fst) snd))
    (pair (pair (fst.comp (fst.comp fst)) (fst.comp snd)) (snd.comp snd))

theorem captureCalls_smaller (parameter : String × ℕ) (pattern : Pattern) :
    ∀ call ∈ captureCalls parameter pattern, patternCode call.2 < patternCode pattern := by
  intro call member
  simp only [captureCalls, List.mem_map] at member
  obtain ⟨inner, inside, rfl⟩ := member
  exact underCalls_smaller _ _ _ inner inside

theorem captureCombine_computable :
    CodeComputable fun input : (String × ℕ) × Pattern × List (Option ℕ) =>
      captureCombine input.1 input.2.1 input.2.2 := by
  have first : CodeComputable fun input : (String × ℕ) × Pattern × List (Option ℕ) => input.2.2.findSome? id :=
    list_findSome? (snd.comp snd) snd
  have named : CodeComputable₂ fun (input : (String × ℕ) × Pattern × List (Option ℕ)) (other : String) =>
      if other == input.1.1 then some input.1.2 else (none : Option ℕ) :=
    CodeComputable.ite (stringBEq.comp (pair snd (fst.comp (fst.comp fst)))) (option_some (snd.comp (fst.comp fst)))
      (const none)
  have restCase : CodeComputable fun x : ((String × ℕ) × Pattern × List (Option ℕ)) × CollType × List Pattern ×
      Option String => Option.casesOn (motive := fun _ => Option ℕ) (x.1.2.2.findSome? id)
        (Option.casesOn (motive := fun _ => Option ℕ) x.2.2.2 none
          fun restName => if restName == x.1.1.1 then some x.1.1.2 else none) some :=
    option_casesOn (first.comp fst) (optionString_casesOn (snd.comp (snd.comp snd)) (const none)
      (named.comp (pair (fst.comp fst) snd))) (option_some snd)
  exact (casesOn (pattern := fun input : (String × ℕ) × Pattern × List (Option ℕ) => input.2.1)
    (onBVar := fun _ _ => (none : Option ℕ))
    (onFVar := fun input other => if other == input.1.1 then some input.1.2 else none)
    (onApply := fun input _ _ => input.2.2.findSome? id) (onLambda := fun input _ _ => input.2.2.findSome? id)
    (onMultiLambda := fun input _ _ _ => input.2.2.findSome? id)
    (onSubst := fun input _ _ => input.2.2.findSome? id)
    (onCollection := fun input _ _ rest => Option.casesOn (motive := fun _ => Option ℕ) (input.2.2.findSome? id)
      (Option.casesOn (motive := fun _ => Option ℕ) rest none
        fun restName => if restName == input.1.1 then some input.1.2 else none) some)
    (fst.comp snd) (const none) named (first.comp fst) (first.comp fst) (first.comp fst) (first.comp fst)
    restCase).of_eq fun _ => rfl

/-- **The depth at which a name is captured is computable on codes.** -/
theorem captureDepth_computable :
    CodeComputable fun input : (String × ℕ) × Pattern => captureDepth input.1.1 input.1.2 input.2 :=
  structural (value := fun parameter pattern => captureDepth parameter.1 parameter.2 pattern)
    (calls := captureCalls) (combine := captureCombine) capture_node captureCalls_smaller captureCalls_computable
    captureCombine_computable

/-! ## Splicing a collection's rest -/

/-- The value bound to a rest name, shifted to the depth of use when it is a closed collection of the kind. -/
def spliceValue (lhs : Pattern) (depth : ℕ) (kind : CollType) (name : String) (value : Pattern) :
    List Pattern × Option String :=
  @Pattern.casesOn (fun _ => List Pattern × Option String) value (fun _ => ([], some name))
    (fun _ => ([], some name)) (fun _ _ => ([], some name)) (fun _ _ => ([], some name))
    (fun _ _ _ => ([], some name)) (fun _ _ => ([], some name))
    (fun boundKind elements boundRest =>
      if boundRest.isNone && boundKind == kind then
        (Option.casesOn (motive := fun _ => List Pattern) (captureDepth name 0 lhs) elements
          fun captured => elements.map (liftBVars 0 (depth - captured)), none)
      else ([], some name))

theorem restSplice_eq (lhs : Pattern) (bindings : Bindings) (depth : ℕ) (kind : CollType) (rest : Option String) :
    restSplice lhs bindings depth kind rest = Option.casesOn (motive := fun _ => List Pattern × Option String) rest
      ([], none) fun name => Option.casesOn (motive := fun _ => List Pattern × Option String)
        (bindings.find? (·.1 == name)) ([], some name) fun entry => spliceValue lhs depth kind name entry.2 := by
  cases rest with
  | none => rfl
  | some name =>
      simp only [restSplice]
      cases bindings.find? (·.1 == name) with
      | none => rfl
      | some entry =>
          obtain ⟨_, value⟩ := entry
          cases value with
          | collection boundKind elements boundRest =>
              cases boundRest with
              | none =>
                  simp only [spliceValue, Option.isNone_none, Bool.true_and]
                  cases captureDepth name 0 lhs <;> rfl
              | some _ => simp [spliceValue]
          | _ => rfl

theorem spliceValue_computable :
    CodeComputable fun input : ((Pattern × ℕ × CollType) × String) × Pattern =>
      spliceValue input.1.1.1 input.1.1.2.1 input.1.1.2.2 input.1.2 input.2 := by
  have stuck : CodeComputable fun input : ((Pattern × ℕ × CollType) × String) × Pattern =>
      (([] : List Pattern), some input.1.2) := pair (const []) (optionString_some (snd.comp fst))
  have closed : CodeComputable fun x : (((Pattern × ℕ × CollType) × String) × Pattern) × CollType × List Pattern ×
      Option String => decide ((code x.2.2.2).unpair.1 = 0) :=
    nat_eq ((of_computable (Primrec.fst.to_comp.comp Primrec.unpair.to_comp)).comp
      ((code' (α := Option String)).comp (snd.comp (snd.comp snd)))) (const 0)
  have sameKind : CodeComputable fun x : (((Pattern × ℕ × CollType) × String) × Pattern) × CollType ×
      List Pattern × Option String => decide (x.2.1 = x.1.1.1.2.2) :=
    (beq_of_injective collectionCode_injective).comp (pair (fst.comp snd) (snd.comp (snd.comp (fst.comp (fst.comp fst)))))
  have captured : CodeComputable fun x : (((Pattern × ℕ × CollType) × String) × Pattern) × CollType ×
      List Pattern × Option String => captureDepth x.1.1.2 0 x.1.1.1.1 :=
    captureDepth_computable.comp (pair (pair (snd.comp (fst.comp fst)) (const 0)) (fst.comp (fst.comp (fst.comp fst))))
  have shiftOne : CodeComputable₂ fun (y : ((((Pattern × ℕ × CollType) × String) × Pattern) × CollType ×
      List Pattern × Option String) × ℕ) (element : Pattern) => liftBVars 0 (y.1.1.1.1.2.1 - y.2) element :=
    (liftBVars'.comp (pair (const 0) (pair (nat_sub (fst.comp (snd.comp (fst.comp (fst.comp (fst.comp
      (fst.comp fst)))))) (snd.comp fst)) snd))).of_eq fun _ => rfl
  have shifted : CodeComputable₂ fun (x : (((Pattern × ℕ × CollType) × String) × Pattern) × CollType ×
      List Pattern × Option String) (capturedDepth : ℕ) =>
      x.2.2.1.map (liftBVars 0 (x.1.1.1.2.1 - capturedDepth)) :=
    list_map (fst.comp (snd.comp (snd.comp fst))) shiftOne
  have elementsOut := option_casesOn captured (fst.comp (snd.comp snd)) shifted
  refine (casesOn (pattern := fun input : ((Pattern × ℕ × CollType) × String) × Pattern => input.2)
    (onBVar := fun input _ => (([] : List Pattern), some input.1.2))
    (onFVar := fun input _ => (([] : List Pattern), some input.1.2))
    (onApply := fun input _ _ => (([] : List Pattern), some input.1.2))
    (onLambda := fun input _ _ => (([] : List Pattern), some input.1.2))
    (onMultiLambda := fun input _ _ _ => (([] : List Pattern), some input.1.2))
    (onSubst := fun input _ _ => (([] : List Pattern), some input.1.2))
    (onCollection := fun input boundKind elements boundRest =>
      if decide ((code boundRest).unpair.1 = 0) && decide (boundKind = input.1.1.2.2) then
        (Option.casesOn (motive := fun _ => List Pattern) (captureDepth input.1.2 0 input.1.1.1) elements
          fun capturedDepth => elements.map (liftBVars 0 (input.1.1.2.1 - capturedDepth)), none)
      else (([] : List Pattern), some input.1.2)) snd (stuck.comp fst) (stuck.comp fst) (stuck.comp fst)
    (stuck.comp fst) (stuck.comp fst) (stuck.comp fst)
    (CodeComputable.ite (CodeComputable.and closed sameKind) (pair elementsOut (const none))
      (stuck.comp fst))).of_eq fun input => ?_
  rcases input with ⟨⟨⟨lhs, depth, kind⟩, name⟩, value⟩
  cases value with
  | collection boundKind elements boundRest =>
      cases boundRest <;> simp [spliceValue, optionStringCode, Nat.unpair_pair]
  | _ => rfl

theorem restSplice_computable :
    CodeComputable fun input : Pattern × Bindings × ℕ × CollType × Option String =>
      restSplice input.1 input.2.1 input.2.2.1 input.2.2.2.1 input.2.2.2.2 := by
  have found : CodeComputable fun x : (Pattern × Bindings × ℕ × CollType × Option String) × String =>
      x.1.2.1.find? (·.1 == x.2) :=
    list_find? (fst.comp (snd.comp fst)) (stringBEq.comp (pair (fst.comp snd) (snd.comp fst)))
  have inner : CodeComputable₂ fun (input : Pattern × Bindings × ℕ × CollType × Option String) (name : String) =>
      Option.casesOn (motive := fun _ => List Pattern × Option String) (input.2.1.find? (·.1 == name))
        ([], some name) fun entry => spliceValue input.1 input.2.2.1 input.2.2.2.1 name entry.2 :=
    option_casesOn found (pair (const []) (optionString_some snd))
      (spliceValue_computable.comp (pair (pair (pair (fst.comp (fst.comp fst)) (pair
        (fst.comp (snd.comp (snd.comp (fst.comp fst)))) (fst.comp (snd.comp (snd.comp (snd.comp (fst.comp fst)))))))
        (snd.comp fst)) (snd.comp snd)))
  exact (optionString_casesOn (snd.comp (snd.comp (snd.comp snd))) (const ([], none)) inner).of_eq fun input =>
    (restSplice_eq input.1 input.2.1 input.2.2.1 input.2.2.2.1 input.2.2.2.2).symm

/-! ## Scope-correct substitution -/

/-- The parts of a right-hand side with the depth below each. -/
def scopedCalls (parameter : Pattern × Bindings × ℕ) (pattern : Pattern) :
    List ((Pattern × Bindings × ℕ) × Pattern) :=
  (underCalls (· + ·) parameter.2.2 pattern).map fun call => ((parameter.1, parameter.2.1, call.1), call.2)

/-- Scope-correct substitution at a node, from the substitutions into its parts. -/
def scopedCombine (parameter : Pattern × Bindings × ℕ) (pattern : Pattern) (values : List Pattern) : Pattern :=
  @Pattern.casesOn (fun _ => Pattern) pattern (fun index => .bvar index)
    (fun name => Option.casesOn (motive := fun _ => Pattern) (parameter.2.1.find? (·.1 == name)) (.fvar name)
      fun entry => Option.casesOn (motive := fun _ => Pattern) (captureDepth name 0 parameter.1) entry.2
        fun captured => liftBVars 0 (parameter.2.2 - captured) entry.2)
    (fun label _ => .apply label values) (fun binder _ => .lambda binder (values.getD 0 (.bvar 0)))
    (fun arity names _ => .multiLambda arity names (values.getD 0 (.bvar 0)))
    (fun _ _ => instantiateBVar (values.getD 1 (.bvar 0)) (values.getD 0 (.bvar 0)))
    (fun kind _ rest => .collection kind
      (values ++ (restSplice parameter.1 parameter.2.1 parameter.2.2 kind rest).1)
      (restSplice parameter.1 parameter.2.1 parameter.2.2 kind rest).2)

theorem scoped_node (parameter : Pattern × Bindings × ℕ) (pattern : Pattern) :
    applyBindingsScoped parameter.1 parameter.2.1 parameter.2.2 pattern = scopedCombine parameter pattern
      ((scopedCalls parameter pattern).map fun call =>
        applyBindingsScoped call.1.1 call.1.2.1 call.1.2.2 call.2) := by
  obtain ⟨lhs, bindings, depth⟩ := parameter
  cases pattern with
  | fvar name =>
      simp only [applyBindingsScoped, scopedCombine]
      cases bindings.find? (·.1 == name) with
      | none => rfl
      | some entry =>
          obtain ⟨_, value⟩ := entry
          simp only []
          cases captureDepth name 0 lhs <;> rfl
  | _ =>
      simp [applyBindingsScoped, applyBindingsScopedList_eq_map, scopedCombine, scopedCalls, underCalls,
        partBinders, parts, zip_zeros, Function.comp_def]

theorem scopedCalls_computable : CodeComputable₂ scopedCalls :=
  list_map ((underCalls_codeComputable Primrec.nat_add.to_comp).comp (pair (snd.comp (snd.comp fst)) snd))
    (pair (pair (fst.comp (fst.comp fst)) (pair (fst.comp (snd.comp (fst.comp fst))) (fst.comp snd))) (snd.comp snd))

theorem scopedCalls_smaller (parameter : Pattern × Bindings × ℕ) (pattern : Pattern) :
    ∀ call ∈ scopedCalls parameter pattern, patternCode call.2 < patternCode pattern := by
  intro call member
  simp only [scopedCalls, List.mem_map] at member
  obtain ⟨inner, inside, rfl⟩ := member
  exact underCalls_smaller _ _ _ inner inside

theorem scopedCombine_computable :
    CodeComputable fun input : (Pattern × Bindings × ℕ) × Pattern × List Pattern =>
      scopedCombine input.1 input.2.1 input.2.2 := by
  have values : CodeComputable fun x : ((Pattern × Bindings × ℕ) × Pattern × List Pattern) × String × List Pattern =>
      x.1.2.2 := snd.comp (snd.comp fst)
  have found : CodeComputable fun x : ((Pattern × Bindings × ℕ) × Pattern × List Pattern) × String =>
      x.1.1.2.1.find? (·.1 == x.2) :=
    list_find? (fst.comp (snd.comp (fst.comp fst))) (stringBEq.comp (pair (fst.comp snd) (snd.comp fst)))
  have shiftValue : CodeComputable₂ fun (y : (((Pattern × Bindings × ℕ) × Pattern × List Pattern) × String) ×
      (String × Pattern)) (captured : ℕ) => liftBVars 0 (y.1.1.1.2.2 - captured) y.2.2 :=
    liftBVars'.comp (pair (const 0) (pair (nat_sub (snd.comp (snd.comp (fst.comp (fst.comp (fst.comp fst)))))
      snd) (snd.comp (snd.comp fst))))
  have bound : CodeComputable₂ fun (x : ((Pattern × Bindings × ℕ) × Pattern × List Pattern) × String)
      (entry : String × Pattern) => Option.casesOn (motive := fun _ => Pattern) (captureDepth x.2 0 x.1.1.1) entry.2
        fun captured => liftBVars 0 (x.1.1.2.2 - captured) entry.2 :=
    option_casesOn (captureDepth_computable.comp (pair (pair (snd.comp fst) (const 0)) (fst.comp (fst.comp (fst.comp fst)))))
      (snd.comp snd) shiftValue
  have spliced : CodeComputable fun x : ((Pattern × Bindings × ℕ) × Pattern × List Pattern) × CollType ×
      List Pattern × Option String => restSplice x.1.1.1 x.1.1.2.1 x.1.1.2.2 x.2.1 x.2.2.2 :=
    restSplice_computable.comp (pair (fst.comp (fst.comp fst)) (pair (fst.comp (snd.comp (fst.comp fst)))
      (pair (snd.comp (snd.comp (fst.comp fst))) (pair (fst.comp snd) (snd.comp (snd.comp snd))))))
  exact (casesOn (pattern := fun input : (Pattern × Bindings × ℕ) × Pattern × List Pattern => input.2.1)
    (onBVar := fun _ index => Pattern.bvar index)
    (onFVar := fun input name => Option.casesOn (motive := fun _ => Pattern) (input.1.2.1.find? (·.1 == name))
      (.fvar name) fun entry => Option.casesOn (motive := fun _ => Pattern) (captureDepth name 0 input.1.1) entry.2
        fun captured => liftBVars 0 (input.1.2.2 - captured) entry.2)
    (onApply := fun input label _ => .apply label input.2.2)
    (onLambda := fun input binder _ => .lambda binder (input.2.2.getD 0 (.bvar 0)))
    (onMultiLambda := fun input arity names _ => .multiLambda arity names (input.2.2.getD 0 (.bvar 0)))
    (onSubst := fun input _ _ => instantiateBVar (input.2.2.getD 1 (.bvar 0)) (input.2.2.getD 0 (.bvar 0)))
    (onCollection := fun input kind _ rest => .collection kind
      (input.2.2 ++ (restSplice input.1.1 input.1.2.1 input.1.2.2 kind rest).1)
      (restSplice input.1.1 input.1.2.1 input.1.2.2 kind rest).2)
    (fst.comp snd) (bvar snd) (option_casesOn found (fvar_computable.comp snd) bound)
    (apply (fst.comp snd) values)
    (lambda (fst.comp snd) (list_getD (Pattern.bvar 0) (snd.comp (snd.comp fst)) (const 0)))
    (multiLambda (fst.comp snd) (fst.comp (snd.comp snd)) (list_getD (Pattern.bvar 0) (snd.comp (snd.comp fst))
      (const 0)))
    (instantiateBVar_computable.comp (pair (list_getD (Pattern.bvar 0) (snd.comp (snd.comp fst)) (const 1))
      (list_getD (Pattern.bvar 0) (snd.comp (snd.comp fst)) (const 0))))
    (collection (fst.comp snd) (list_append (snd.comp (snd.comp fst)) (fst.comp spliced)) (snd.comp spliced))).of_eq
    fun input => by
      rcases input with ⟨parameter, pattern, values⟩
      cases pattern <;> rfl

/-- **Scope-correct substitution is computable on codes.** -/
theorem applyBindingsScoped_computable :
    CodeComputable fun input : (Pattern × Bindings × ℕ) × Pattern =>
      applyBindingsScoped input.1.1 input.1.2.1 input.1.2.2 input.2 :=
  structural (value := fun parameter pattern => applyBindingsScoped parameter.1 parameter.2.1 parameter.2.2 pattern)
    (calls := scopedCalls) (combine := scopedCombine) scoped_node scopedCalls_smaller scopedCalls_computable
    scopedCombine_computable

/-! ## Rules without reflective data -/

open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical in
theorem matchPatternForRule_eq (language : LanguageDef) (rule : RewriteRule) (term : Pattern) :
    matchPatternForRule language rule term = matchPattern rule.left term := by
  simp [matchPatternForRule, matchPatternForRuleUsing, ReflectiveSubstitution.matchingPresentationForRule?,
    ReflectiveSubstitution.reflectiveRuleForRule?]

open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution in
theorem applyBindingsForRule_eq (language : LanguageDef) (rule : RewriteRule) (bindings : Bindings) :
    applyBindingsForRule language rule bindings = applyBindingsScoped rule.left bindings 0 rule.right := by
  simp [applyBindingsForRule, applyRuleBindings]

/-- **Matching a fixed rule against a term is computable on codes.** -/
theorem matchPatternForRule_computable (language : LanguageDef) (rule : RewriteRule) :
    CodeComputable fun term : Pattern => ReflectiveCanonical.matchPatternForRule language rule term :=
  (matchPattern_computable.comp (pair (const rule.left) id)).of_eq fun term =>
    (matchPatternForRule_eq language rule term).symm

/-- **Building a fixed rule's reduct from bindings is computable on codes.** -/
theorem applyBindingsForRule_computable (language : LanguageDef) (rule : RewriteRule) :
    CodeComputable fun bindings : Bindings => ReflectiveSubstitution.applyBindingsForRule language rule bindings :=
  (applyBindingsScoped_computable.comp (pair (pair (const rule.left) (pair id (const 0))) (const rule.right))).of_eq
    fun bindings => (applyBindingsForRule_eq language rule bindings).symm

end Mettapedia.OSLF.MeTTaIL.EngineCoded
