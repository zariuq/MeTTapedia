import Mettapedia.Computability.Coded
import Mettapedia.OSLF.MeTTaIL.PatternLexOrderComputable

/-!
# Patterns as coded values

A pattern is coded by its structural code, a string by the code of its characters, an optional string, a collection
kind and a list of strings by their codes in the pattern code (`Coded Pattern`, …). With these codes each constructor
of patterns is computable on codes (`apply_codeComputable`, …), and so is a definition by cases on a pattern
(`casesOn`): the code of a pattern is its constructor's tag paired with the code of its fields.

A function given by structural recursion on patterns, with a parameter, is computable on codes when its calls and its
combination are (`structural`). Shifting and renaming bound variables, the serialization, the order of patterns,
sorting by it and equality are computable on codes.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.PatternCode

open Mettapedia.Computability
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.PatternLexOrder

instance : Coded Pattern := ⟨patternCode⟩
instance : Coded String := ⟨stringCode⟩
instance : Coded (Option String) := ⟨optionStringCode⟩
instance : Coded CollType := ⟨collectionCode⟩

@[simp] theorem code_pattern (pattern : Pattern) : code pattern = patternCode pattern := rfl
@[simp] theorem code_string (string : String) : code string = stringCode string := rfl
@[simp] theorem code_optionString (string : Option String) : code string = optionStringCode string := rfl
@[simp] theorem code_collType (kind : CollType) : code kind = collectionCode kind := rfl

theorem code_patterns (patterns : List Pattern) : code patterns = patternListCode patterns := by
  rw [code_list, patternListCode_eq_encode]; rfl

theorem code_strings (strings : List String) : code strings = stringListCode strings := by
  rw [code_list, stringListCode_eq_encode]; rfl

theorem patternCode_injective' : Function.Injective (code : Pattern → ℕ) := patternCode_injective

theorem stringCode_injective' : Function.Injective (code : String → ℕ) := stringCode_injective

namespace CodeComputable'

open CodeComputable

variable {α β : Type*} [Coded α] [Coded β]

/-! ## Constructors -/

private theorem tagged (tag : ℕ) {fields : α → ℕ} (computable : CodeComputable fields) :
    CodeComputable fun argument => Nat.pair tag (fields argument) :=
  (of_computable₂ Primrec₂.natPair.to_comp).comp ((const tag).pair computable)

theorem bvar {index : α → ℕ} (hIndex : CodeComputable index) :
    CodeComputable fun argument => Pattern.bvar (index argument) :=
  (tagged 0 hIndex).of_eq fun _ => rfl

theorem apply {label : α → String} {arguments : α → List Pattern} (hLabel : CodeComputable label)
    (hArguments : CodeComputable arguments) :
    CodeComputable fun argument => Pattern.apply (label argument) (arguments argument) := by
  obtain ⟨track, computable, tracks⟩ := hLabel.pair hArguments
  refine ⟨fun n => Nat.pair 2 (track n), Primrec₂.natPair.to_comp.comp (Computable.const 2) computable,
    fun argument => ?_⟩
  beta_reduce
  rw [tracks, code_pair, code_patterns]; rfl

theorem lambda {binder : α → Option String} {body : α → Pattern} (hBinder : CodeComputable binder)
    (hBody : CodeComputable body) :
    CodeComputable fun argument => Pattern.lambda (binder argument) (body argument) := by
  obtain ⟨track, computable, tracks⟩ := hBinder.pair hBody
  exact ⟨fun n => Nat.pair 3 (track n), Primrec₂.natPair.to_comp.comp (Computable.const 3) computable,
    fun argument => by beta_reduce; rw [tracks]; rfl⟩

theorem multiLambda {arity : α → ℕ} {binders : α → List String} {body : α → Pattern}
    (hArity : CodeComputable arity) (hBinders : CodeComputable binders) (hBody : CodeComputable body) :
    CodeComputable fun argument => Pattern.multiLambda (arity argument) (binders argument) (body argument) := by
  obtain ⟨track, computable, tracks⟩ := hArity.pair (hBinders.pair hBody)
  refine ⟨fun n => Nat.pair 4 (track n), Primrec₂.natPair.to_comp.comp (Computable.const 4) computable,
    fun argument => ?_⟩
  beta_reduce
  rw [tracks, code_pair, code_pair, code_strings]; rfl

theorem subst {body replacement : α → Pattern} (hBody : CodeComputable body)
    (hReplacement : CodeComputable replacement) :
    CodeComputable fun argument => Pattern.subst (body argument) (replacement argument) := by
  obtain ⟨track, computable, tracks⟩ := hBody.pair hReplacement
  exact ⟨fun n => Nat.pair 5 (track n), Primrec₂.natPair.to_comp.comp (Computable.const 5) computable,
    fun argument => by beta_reduce; rw [tracks]; rfl⟩

theorem collection {kind : α → CollType} {elements : α → List Pattern} {rest : α → Option String}
    (hKind : CodeComputable kind) (hElements : CodeComputable elements) (hRest : CodeComputable rest) :
    CodeComputable fun argument => Pattern.collection (kind argument) (elements argument) (rest argument) := by
  obtain ⟨track, computable, tracks⟩ := hKind.pair (hElements.pair hRest)
  refine ⟨fun n => Nat.pair 6 (track n), Primrec₂.natPair.to_comp.comp (Computable.const 6) computable,
    fun argument => ?_⟩
  beta_reduce
  rw [tracks, code_pair, code_pair, code_patterns]; rfl

/-! ## Cases on a pattern -/

/-- **A definition by cases on a pattern is computable on codes** when each case is, as a function of the
argument and the constructor's fields. -/
theorem casesOn {pattern : α → Pattern} {onBVar : α → ℕ → β} {onFVar : α → String → β}
    {onApply : α → String → List Pattern → β} {onLambda : α → Option String → Pattern → β}
    {onMultiLambda : α → ℕ → List String → Pattern → β} {onSubst : α → Pattern → Pattern → β}
    {onCollection : α → CollType → List Pattern → Option String → β} (hPattern : CodeComputable pattern)
    (hBVar : CodeComputable₂ onBVar) (hFVar : CodeComputable₂ onFVar)
    (hApply : CodeComputable fun input : α × String × List Pattern => onApply input.1 input.2.1 input.2.2)
    (hLambda : CodeComputable fun input : α × Option String × Pattern => onLambda input.1 input.2.1 input.2.2)
    (hMultiLambda : CodeComputable fun input : α × ℕ × List String × Pattern =>
      onMultiLambda input.1 input.2.1 input.2.2.1 input.2.2.2)
    (hSubst : CodeComputable fun input : α × Pattern × Pattern => onSubst input.1 input.2.1 input.2.2)
    (hCollection : CodeComputable fun input : α × CollType × List Pattern × Option String =>
      onCollection input.1 input.2.1 input.2.2.1 input.2.2.2) :
    CodeComputable fun argument => @Pattern.casesOn (fun _ => β) (pattern argument) (onBVar argument)
      (onFVar argument) (onApply argument) (onLambda argument) (onMultiLambda argument) (onSubst argument)
      (onCollection argument) := by
  obtain ⟨trackPattern, computablePattern, tracksPattern⟩ := hPattern
  obtain ⟨track0, computable0, tracks0⟩ := hBVar
  obtain ⟨track1, computable1, tracks1⟩ := hFVar
  obtain ⟨track2, computable2, tracks2⟩ := hApply
  obtain ⟨track3, computable3, tracks3⟩ := hLambda
  obtain ⟨track4, computable4, tracks4⟩ := hMultiLambda
  obtain ⟨track5, computable5, tracks5⟩ := hSubst
  obtain ⟨track6, computable6, tracks6⟩ := hCollection
  let fields : ℕ → ℕ := fun n => Nat.pair n (trackPattern n).unpair.2
  have fieldsComputable : Computable fields :=
    Primrec₂.natPair.to_comp.comp Computable.id (Primrec.snd.to_comp.comp (Primrec.unpair.to_comp.comp
      computablePattern))
  have tagOf : Computable fun n => (trackPattern n).unpair.1 :=
    Primrec.fst.to_comp.comp (Primrec.unpair.to_comp.comp computablePattern)
  have isTag : ∀ value : ℕ, Computable fun n => (trackPattern n).unpair.1 == value :=
    fun value => (Primrec.beq.to_comp).comp tagOf (Computable.const value)
  refine ⟨fun n => _root_.cond ((trackPattern n).unpair.1 == 0) (track0 (fields n))
      (_root_.cond ((trackPattern n).unpair.1 == 1) (track1 (fields n))
      (_root_.cond ((trackPattern n).unpair.1 == 2) (track2 (fields n))
      (_root_.cond ((trackPattern n).unpair.1 == 3) (track3 (fields n))
      (_root_.cond ((trackPattern n).unpair.1 == 4) (track4 (fields n))
      (_root_.cond ((trackPattern n).unpair.1 == 5) (track5 (fields n)) (track6 (fields n))))))), ?_, ?_⟩
  · exact Computable.cond (isTag 0) (computable0.comp fieldsComputable)
      (Computable.cond (isTag 1) (computable1.comp fieldsComputable)
      (Computable.cond (isTag 2) (computable2.comp fieldsComputable)
      (Computable.cond (isTag 3) (computable3.comp fieldsComputable)
      (Computable.cond (isTag 4) (computable4.comp fieldsComputable)
      (Computable.cond (isTag 5) (computable5.comp fieldsComputable) (computable6.comp fieldsComputable))))))
  · intro argument
    beta_reduce
    simp only [fields]
    rw [tracksPattern]
    cases pattern argument with
    | bvar index => simpa [patternCode, code_pair] using tracks0 (argument, index)
    | fvar name => simpa [patternCode, code_pair] using tracks1 (argument, name)
    | apply label arguments => simpa [patternCode, code_pair, code_patterns] using tracks2 (argument, label, arguments)
    | lambda binder body => simpa [patternCode, code_pair] using tracks3 (argument, binder, body)
    | multiLambda arity binders body =>
        simpa [patternCode, code_pair, code_strings] using tracks4 (argument, arity, binders, body)
    | subst body replacement => simpa [patternCode, code_pair] using tracks5 (argument, body, replacement)
    | collection kind elements rest =>
        simpa [patternCode, code_pair, code_patterns] using tracks6 (argument, kind, elements, rest)

/-! ## Structural recursion -/

/-- The machine of a structural recursion on codes, within a fuel. -/
def structuralRun (trackCalls trackCombine : ℕ → ℕ) : ℕ → ℕ → ℕ :=
  FuelRecursion.run (fun _ => 0) (fun _ n => Denumerable.ofNat (List ℕ) (trackCalls n))
    (fun _ n values => trackCombine (Nat.pair n.unpair.1 (Nat.pair n.unpair.2 (Encodable.encode values))))

theorem structuralRun_succ (trackCalls trackCombine : ℕ → ℕ) (fuel n : ℕ) :
    structuralRun trackCalls trackCombine (fuel + 1) n =
      trackCombine (Nat.pair n.unpair.1 (Nat.pair n.unpair.2 (Encodable.encode
        ((Denumerable.ofNat (List ℕ) (trackCalls n)).map (structuralRun trackCalls trackCombine fuel))))) :=
  FuelRecursion.run_succ _ _ _ fuel n

theorem structuralRun_computable {trackCalls trackCombine : ℕ → ℕ} (computableCalls : Computable trackCalls)
    (computableCombine : Computable trackCombine) : Computable₂ (structuralRun trackCalls trackCombine) :=
  FuelRecursion.run_computable (Computable.const 0)
    ((Primrec.ofNat (List ℕ)).to_comp.comp (computableCalls.comp Computable.snd))
    (computableCombine.comp (Primrec₂.natPair.to_comp.comp
      (Primrec.fst.to_comp.comp (Primrec.unpair.to_comp.comp (Computable.fst.comp Computable.snd)))
      (Primrec₂.natPair.to_comp.comp
        (Primrec.snd.to_comp.comp (Primrec.unpair.to_comp.comp (Computable.fst.comp Computable.snd)))
        (Primrec.encode.to_comp.comp (Computable.snd.comp Computable.snd)))))

/-- **Structural recursion on patterns is computable on codes**: at every pattern the function is a combination,
computable on codes, of its values at calls, computable on codes, to patterns of smaller code. -/
theorem structural {value : α → Pattern → β} {calls : α → Pattern → List (α × Pattern)}
    {combine : α → Pattern → List β → β}
    (node : ∀ parameter pattern, value parameter pattern =
      combine parameter pattern ((calls parameter pattern).map fun call => value call.1 call.2))
    (smaller : ∀ parameter pattern, ∀ call ∈ calls parameter pattern, patternCode call.2 < patternCode pattern)
    (hCalls : CodeComputable₂ calls)
    (hCombine : CodeComputable fun input : α × Pattern × List β => combine input.1 input.2.1 input.2.2) :
    CodeComputable₂ value := by
  obtain ⟨trackCalls, computableCalls, tracksCalls⟩ := hCalls
  obtain ⟨trackCombine, computableCombine, tracksCombine⟩ := hCombine
  have runs : ∀ fuel parameter pattern, patternCode pattern < fuel →
      structuralRun trackCalls trackCombine fuel (Nat.pair (code parameter) (patternCode pattern)) =
        code (value parameter pattern) := by
    intro fuel
    induction fuel with
    | zero => intro _ _ impossible; exact absurd impossible (Nat.not_lt_zero _)
    | succ fuel recurse =>
        intro parameter pattern bounded
        rw [structuralRun_succ]
        have callsTracked : trackCalls (Nat.pair (code parameter) (patternCode pattern)) =
            code (calls parameter pattern) := tracksCalls (parameter, pattern)
        rw [callsTracked, ofNat_code_list, List.map_map]
        have values : (calls parameter pattern).map (structuralRun trackCalls trackCombine fuel ∘ code) =
            (calls parameter pattern).map (code ∘ fun call => value call.1 call.2) :=
          List.map_congr_left fun call member => by
            simp only [Function.comp_apply, code_pair, code_pattern]
            exact recurse call.1 call.2 (Nat.lt_of_lt_of_le (smaller parameter pattern call member)
              (Nat.lt_succ_iff.mp bounded))
        rw [values, ← List.map_map]
        simp only [Nat.unpair_pair]
        have combined : trackCombine (Nat.pair (code parameter) (Nat.pair (patternCode pattern)
            (Encodable.encode (((calls parameter pattern).map fun call => value call.1 call.2).map code)))) =
            code (combine parameter pattern ((calls parameter pattern).map fun call => value call.1 call.2)) :=
          tracksCombine (parameter, pattern, (calls parameter pattern).map fun call => value call.1 call.2)
        rw [combined, ← node]
  refine ⟨fun n => structuralRun trackCalls trackCombine (n.unpair.2 + 1) n, ?_, fun pair => ?_⟩
  · exact (structuralRun_computable computableCalls computableCombine).comp
      (Primrec.succ.to_comp.comp (Primrec.snd.to_comp.comp Primrec.unpair.to_comp)) Computable.id
  · beta_reduce
    rw [code_pair, code_pattern, Nat.unpair_pair]
    exact runs _ pair.1 pair.2 (Nat.lt_succ_self _)

/-! ## Operations on patterns -/

theorem liftBVars' : CodeComputable fun input : ℕ × ℕ × Pattern =>
    Substitution.liftBVars input.1 input.2.1 input.2.2 :=
  ⟨fun n => liftCode n.unpair.1 n.unpair.2.unpair.1 n.unpair.2.unpair.2,
    Computable.comp (f := fun triple : ℕ × ℕ × ℕ => liftCode triple.1 triple.2.1 triple.2.2)
      (g := fun n : ℕ => (n.unpair.1, n.unpair.2.unpair.1, n.unpair.2.unpair.2)) liftCode_computable
      (Computable.pair (Primrec.fst.to_comp.comp Primrec.unpair.to_comp)
        (Computable.pair (Primrec.fst.to_comp.comp (Primrec.unpair.to_comp.comp (Primrec.snd.to_comp.comp
          Primrec.unpair.to_comp))) (Primrec.snd.to_comp.comp (Primrec.unpair.to_comp.comp
            (Primrec.snd.to_comp.comp Primrec.unpair.to_comp))))),
    fun input => by simp [code_pair, liftCode_patternCode]⟩

/-- **Renaming the bound variables by a computable family is computable on codes.** -/
theorem rename' {relabel : ℕ → ℕ → ℕ} (hRelabel : Computable₂ relabel) :
    CodeComputable fun input : ℕ × Pattern =>
      ContextSubstitution.substitute (fun index => .bvar (relabel input.1 index)) input.2 :=
  ⟨fun n => renameCode relabel n.unpair.1 n.unpair.2,
    Computable.comp (f := fun pair : ℕ × ℕ => renameCode relabel pair.1 pair.2)
      (g := fun n : ℕ => (n.unpair.1, n.unpair.2)) (renameCode_computable hRelabel)
      (Computable.pair (Primrec.fst.to_comp.comp Primrec.unpair.to_comp)
        (Primrec.snd.to_comp.comp Primrec.unpair.to_comp)),
    fun input => by simp [code_pair, renameCode_patternCode]⟩

theorem ser' : CodeComputable fun pattern : Pattern => ser pattern :=
  ⟨serCode, serCode_computable, fun pattern => by
    beta_reduce
    rw [code_pattern, serCode_patternCode, code_list]
    exact congrArg _ (List.map_id _).symm⟩

theorem patternLe' : CodeComputable₂ fun left right : Pattern => decide (PatternLe left right) :=
  ⟨fun n => _root_.cond (leCode n.unpair.1 n.unpair.2) 1 0,
    Computable.cond (leCode_computable.comp (Primrec.fst.to_comp.comp Primrec.unpair.to_comp)
      (Primrec.snd.to_comp.comp Primrec.unpair.to_comp)) (Computable.const 1) (Computable.const 0),
    fun pair => by
      simp only [code_pair, code_pattern, Nat.unpair_pair, leCode, serOf_patternCode, PatternLe]
      rcases Bool.eq_false_or_eq_true (lexLe (ser pair.1) (ser pair.2)) with same | same <;> simp [same]⟩

theorem insertionSort' : CodeComputable fun patterns : List Pattern => patterns.insertionSort PatternLe :=
  ⟨fun n => Encodable.encode (sortCode (Denumerable.ofNat (List ℕ) n)),
    Primrec.encode.to_comp.comp (sortCode_computable.comp (Primrec.ofNat (List ℕ)).to_comp),
    fun patterns => by
      beta_reduce
      rw [ofNat_code_list]
      show Encodable.encode (sortCode (patterns.map patternCode)) = _
      rw [sortCode_patternCode]; rfl⟩

theorem patternEq : CodeComputable₂ fun left right : Pattern => decide (left = right) :=
  beq_of_injective patternCode_injective'

theorem stringEq : CodeComputable₂ fun left right : String => decide (left = right) :=
  beq_of_injective stringCode_injective'

end CodeComputable'

end Mettapedia.OSLF.MeTTaIL.PatternCode
