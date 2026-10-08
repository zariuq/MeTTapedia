import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.MMBUnificationSoundness

/-!
# Actual MMB theorem-premise consumption

Hypothesis commands consume completed proofs from the retained main stack.
The source decoder lists hypotheses from last to first; the existing kernel
list judgment receives their ordered substituted images. Theorem application
composes this evidence with an independently available declaration and
admissible arguments. Deriving dependency safety from the machine checks is
a separate obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.MMBTheoremSoundness

open Formats.MMB
open Kernel
open MMBMachineSoundness MMBUnificationSoundness

theorem stack_pop_proof (signature : TermSignature) (definitions : Definition.Signature)
    (theorems : TheoremSignature) (context : Context) (hypotheses : List Preterm)
    (store : List Alloc) (position : Nat) (rest : List Elem)
    (sound : StackSound signature definitions theorems context hypotheses store (.proof position :: rest)) :
    ProvenPointer signature definitions theorems context hypotheses store position ∧
      StackSound signature definitions theorems context hypotheses store rest := by
  cases sound with
  | proof proved tail => exact ⟨proved, tail⟩

theorem unify_apply_hyp (store : List Alloc) (before after : Unifier)
    (empty : before.stack = []) (executed : unifyStep store .apply before .hyp = some after) :
    ∃ position rest, before.main = .proof position :: rest ∧
      after = { before with stack := [position], main := rest } := by
  change (match before.main with
    | .proof position :: rest => some { before with stack := position :: before.stack, main := rest }
    | _ => none) = some after at executed
  split at executed
  · rename_i position rest shape
    exact ⟨position, rest, shape, by simpa [empty] using (Option.some.inj executed).symm⟩
  · cases executed

/-- The terminal empty-stack check is part of the retained runner. -/
theorem unifyRun_empty_stack (store : List Alloc) (mode : UMode)
    (before after : Unifier) (commands : List UnifyCmd)
    (accepted : unifyRun store mode before commands = some after) : after.stack = [] := by
  rw [unifyRun_fold] at accepted
  obtain ⟨middle, _, checked⟩ := Option.bind_eq_some_iff.mp accepted
  split at checked
  · rename_i finished
    have same : middle = after := Option.some.inj checked
    subst after
    exact finished.1
  · cases checked

theorem derivesList_append (signature : TermSignature) (definitions : Definition.Signature)
    (theorems : TheoremSignature) (context : Context) (hypotheses first rest : List Preterm)
    (firstProofs : DerivesList signature definitions theorems context hypotheses first)
    (restProofs : DerivesList signature definitions theorems context hypotheses rest) :
    DerivesList signature definitions theorems context hypotheses (first ++ rest) := by
  induction first with
  | nil => exact restProofs
  | cons expression expressions ih =>
      cases firstProofs with
      | cons head tail => exact .cons head (ih tail)

/-- Every actual proof consumed by `UHyp` supplies a completed kernel
derivation of the corresponding substituted source hypothesis. -/
theorem decodeHyps_apply_derives (signature : TermSignature) (definitions : Definition.Signature)
    (theorems : TheoremSignature) (context : Context) (hypotheses : List Preterm)
    (store : List Alloc) (typed : TypedStore signature context store)
    (arity : Nat → Option Nat)
    (arities : ∀ term declaration, signature term = some declaration → arity term = some declaration.arguments.length)
    (substitution : Substitution) (arguments fuel : Nat)
    (sourceBefore : Statements.Decoding) (commands : List UnifyCmd) (sources : List Preterm)
    (before after : Unifier)
    (decoded : Statements.decodeHyps arity arguments fuel sourceBefore commands = some sources)
    (accepted : unifyRun store .apply before commands = some after)
    (empty : before.stack = [])
    (matching : SlotsSubstitute store substitution sourceBefore.slots before.heap)
    (sound : StackSound signature definitions theorems context hypotheses store before.main) :
    ∃ images, List.Forall₂ (Preterm.Substitutes substitution) sources images ∧
      DerivesList signature definitions theorems context hypotheses images ∧
      StackSound signature definitions theorems context hypotheses store after.main ∧
      after.hyps = before.hyps := by
  cases commands with
  | nil =>
      have sameSources : [] = sources := by simpa [Statements.decodeHyps] using decoded
      subst sources
      have sameAfter : before = after := by simpa [unifyRun, empty] using accepted
      subst after
      exact ⟨[], .nil, .nil, sound, rfl⟩
  | cons command commands =>
      cases fuel with
      | zero => simp [Statements.decodeHyps] at decoded
      | succ fuel =>
          cases command with
          | term term => simp [Statements.decodeHyps] at decoded
          | termSave term => simp [Statements.decodeHyps] at decoded
          | ref index => simp [Statements.decodeHyps] at decoded
          | dummy sort => simp [Statements.decodeHyps] at decoded
          | hyp =>
              cases first : Statements.decodeExpr arity arguments fuel sourceBefore commands with
              | none => simp [Statements.decodeHyps, first] at decoded
              | some value =>
                  rcases value with ⟨source, middleSource, remaining⟩
                  cases others : Statements.decodeHyps arity arguments fuel middleSource remaining with
                  | none => simp [Statements.decodeHyps, first, others] at decoded
                  | some earlier =>
                      have sameSources : earlier ++ [source] = sources := by
                        simpa [Statements.decodeHyps, first, others] using decoded
                      subst sources
                      cases firstStep : unifyStep store .apply before .hyp with
                      | none => simp [unifyRun, firstStep] at accepted
                      | some started =>
                          have restAccepted : unifyRun store .apply started commands = some after := by
                            simpa [unifyRun, firstStep] using accepted
                          obtain ⟨position, rest, shape, sameStarted⟩ := unify_apply_hyp store before started empty firstStep
                          subst started
                          have shaped : StackSound signature definitions theorems context hypotheses store (.proof position :: rest) := shape ▸ sound
                          obtain ⟨proved, restSound⟩ := stack_pop_proof signature definitions theorems context hypotheses store position rest shaped
                          obtain ⟨proofImage, sort, proofRead, _, derivation⟩ := proved
                          obtain ⟨_, consumed, _, consumedRead, _⟩ :=
                            Soundness.decodeExpr_source_order arity arguments fuel sourceBefore middleSource commands remaining source first
                          have expressionAccepted : unifyRun store .apply { before with stack := [position], main := rest }
                              (consumed ++ remaining) = some after := by rw [← consumedRead]; exact restAccepted
                          obtain ⟨middle, expressionSteps, remainingAccepted⟩ :=
                            unifyRun_prefix store .apply { before with stack := [position], main := rest } after consumed remaining expressionAccepted
                          have sourceRead : Statements.decodeExpr arity arguments fuel sourceBefore (consumed ++ remaining) =
                              some (source, middleSource, remaining) := by rw [← consumedRead]; exact first
                          obtain ⟨image, imageRead, substituted, middleStack, middleSlots, middleMain, middleHyps, _⟩ :=
                            decodeExpr_unifies signature context store typed arity arities substitution .apply (by decide)
                              arguments fuel sourceBefore middleSource consumed remaining source _ middle position []
                              sourceRead expressionSteps rfl matching
                          have sameImage : proofImage = image := Option.some.inj (proofRead.symm.trans imageRead)
                          subst proofImage
                          have middleSound : StackSound signature definitions theorems context hypotheses store middle.main := by
                            rw [middleMain]
                            exact restSound
                          obtain ⟨images, otherSubstituted, otherProofs, afterSound, afterHyps⟩ :=
                            decodeHyps_apply_derives signature definitions theorems context hypotheses store typed arity arities substitution
                              arguments fuel middleSource remaining earlier middle after others remainingAccepted middleStack middleSlots middleSound
                          exact ⟨images ++ [image], List.rel_append otherSubstituted (.cons substituted .nil),
                            derivesList_append signature definitions theorems context hypotheses images [image] otherProofs (.cons derivation .nil),
                            afterSound, afterHyps.trans middleHyps⟩
termination_by fuel

/-- The actual theorem unifier consumes proof premises and establishes the
decoded declaration's simultaneous substitution. Availability and dependency
safety are separate inputs, not consequences attributed to the unifier. -/
theorem unify_theorem_proven (signature : TermSignature) (definitions : Definition.Signature)
    (theorems : TheoremSignature) (context : Context) (hypotheses : List Preterm)
    (store : List Alloc) (typed : TypedStore signature context store)
    (terms : List TermEntry) (entry : ThmEntry) (declaration : TheoremDecl) (theorem_ : Nat)
    (arities : ∀ term termDeclaration, signature term = some termDeclaration →
      Statements.arityOf terms term = some termDeclaration.arguments.length)
    (declared : Statements.theoremDecl terms entry = some declaration)
    (available : theorems theorem_ = some declaration)
    (positions : List Nat) (images : List Preterm) (position : Nat)
    (main : List Elem) (hyps : List Nat) (after : Unifier)
    (lengths : positions.length = entry.args.length)
    (argumentsRead : positions.mapM (Soundness.decode store) = some images)
    (admissible : Substitution.Admissible signature declaration.arguments context images)
    (sound : StackSound signature definitions theorems context hypotheses store main)
    (accepted : unifyRun store .apply ⟨[position], positions.map (·, false), main, hyps⟩ entry.unify = some after) :
    ProvenPointer signature definitions theorems context hypotheses store position ∧
      StackSound signature definitions theorems context hypotheses store after.main ∧
      after.hyps = hyps := by
  let fuel := 2 * entry.unify.length + 2
  cases conclusion : Statements.decodeExpr (Statements.arityOf terms) entry.args.length fuel
      (Statements.initial entry.args.length) entry.unify with
  | none => simp [Statements.theoremDecl, fuel, conclusion] at declared
  | some value =>
      rcases value with ⟨source, middleSource, remaining⟩
      have sourceDecl : (if middleSource.dummies ≠ [] then none else
          (Statements.decodeHyps (Statements.arityOf terms) entry.args.length fuel middleSource remaining).bind
            (fun hypotheses => some (⟨Statements.context entry.args, hypotheses, source⟩ : TheoremDecl))) =
          some declaration := by
        change (Statements.decodeExpr (Statements.arityOf terms) entry.args.length fuel
          (Statements.initial entry.args.length) entry.unify).bind _ = some declaration at declared
        rw [conclusion, Option.bind_some] at declared
        exact declared
      split at sourceDecl
      · cases sourceDecl
      · cases sourcesRead : Statements.decodeHyps (Statements.arityOf terms) entry.args.length fuel middleSource remaining with
        | none => simp [sourcesRead] at sourceDecl
        | some sources =>
            have sameDeclaration : (⟨Statements.context entry.args, sources, source⟩ : TheoremDecl) = declaration := by
              simpa [sourcesRead] using sourceDecl
            obtain ⟨_, consumed, _, consumedRead, _⟩ :=
              Soundness.decodeExpr_source_order (Statements.arityOf terms) entry.args.length fuel
                (Statements.initial entry.args.length) middleSource entry.unify remaining source conclusion
            have prefixAccepted : unifyRun store .apply ⟨[position], positions.map (·, false), main, hyps⟩
                (consumed ++ remaining) = some after := by rw [← consumedRead]; exact accepted
            obtain ⟨middle, expressionSteps, remainingAccepted⟩ :=
              unifyRun_prefix store .apply ⟨[position], positions.map (·, false), main, hyps⟩ after consumed remaining prefixAccepted
            have expressionRead : Statements.decodeExpr (Statements.arityOf terms) entry.args.length fuel
                (Statements.initial entry.args.length) (consumed ++ remaining) = some (source, middleSource, remaining) := by
              rw [← consumedRead]
              exact conclusion
            have initialSlots : SlotsSubstitute store (Substitution.ofList images)
                (Statements.initial entry.args.length).slots (positions.map (·, false)) := by
              rw [← lengths]
              exact SlotsSubstitute.initial store positions images argumentsRead
            obtain ⟨image, imageRead, substituted, middleStack, middleSlots, middleMain, middleHyps, _⟩ :=
              decodeExpr_unifies signature context store typed (Statements.arityOf terms) arities (Substitution.ofList images)
                .apply (by decide) entry.args.length fuel (Statements.initial entry.args.length) middleSource
                consumed remaining source _ middle position [] expressionRead expressionSteps rfl initialSlots
            have middleSound : StackSound signature definitions theorems context hypotheses store middle.main := by
              rw [middleMain]
              exact sound
            obtain ⟨premises, premisesSubstituted, premisesDerived, afterSound, afterHyps⟩ :=
              decodeHyps_apply_derives signature definitions theorems context hypotheses store typed (Statements.arityOf terms)
                arities (Substitution.ofList images) entry.args.length fuel middleSource remaining sources middle after
                sourcesRead remainingAccepted middleStack middleSlots middleSound
            have instantiated : TheoremDecl.Instantiates signature context declaration images ⟨premises, image⟩ := by
              rw [← sameDeclaration] at admissible ⊢
              exact ⟨admissible, premisesSubstituted, substituted⟩
            have derived : Derives signature definitions theorems context hypotheses image :=
              .theoremApp available instantiated premisesDerived
            have inside : position < store.length := decoded_pointer_allocated store position image imageRead
            obtain ⟨typedImage, typedRead, typing, _⟩ := typed.expression position (store[position]'inside) (List.getElem?_eq_getElem inside)
            have sameImage : typedImage = image := Option.some.inj (typedRead.symm.trans imageRead)
            subst typedImage
            exact ⟨⟨image, (store[position]'inside).type.sort, imageRead, typing, derived⟩,
              afterSound, afterHyps.trans middleHyps⟩

namespace Controls

private def constantType : ExprType := ⟨0, false, ∅⟩
private def termDeclaration : TermDecl := ⟨[], 0, ∅⟩
private def terms : List TermEntry := List.replicate 3 ⟨0, [], constantType, none⟩
private def signature : TermSignature := fun term =>
  if term = 0 ∨ term = 1 ∨ term = 2 then some termDeclaration else none
private def premiseDeclaration (term : Nat) : TheoremDecl := ⟨[], [], .term term⟩
private def declaration : TheoremDecl := ⟨[], [.term 0, .term 1], .term 2⟩
private def theorems : TheoremSignature := fun index =>
  if index = 0 then some (premiseDeclaration 0) else if index = 1 then some (premiseDeclaration 1)
  else if index = 2 then some declaration else none
private def entry : ThmEntry := ⟨[], [.term 2, .hyp, .term 1, .hyp, .term 0]⟩
private def store : List Alloc :=
  [⟨.app 0 [], constantType⟩, ⟨.app 1 [], constantType⟩, ⟨.app 2 [], constantType⟩]
private def before : Unifier := ⟨[2], [], [.proof 1, .proof 0], [1, 0]⟩
private def after : Unifier := ⟨[], [], [], [1, 0]⟩

private theorem constant_decodes (position : Nat) (inside : position < 3) :
    Soundness.decode store position = some (.term position) := by
  cases position with
  | zero => rw [Soundness.decode]; rfl
  | succ position =>
      cases position with
      | zero => rw [Soundness.decode]; rfl
      | succ position =>
          cases position with
          | zero => rw [Soundness.decode]; rfl
          | succ position => omega

private theorem typed : TypedStore signature [] store := by
  constructor
  intro position allocation found
  have inside : position < 3 := by
    have bound := (List.getElem?_eq_some_iff.mp found).choose
    simpa [store] using bound
  have sort : allocation.type.sort = 0 := by
    cases position with
    | zero => simp [store] at found; cases found; rfl
    | succ position =>
        cases position with
        | zero => simp [store] at found; cases found; rfl
        | succ position =>
            cases position with
            | zero => simp [store] at found; cases found; rfl
            | succ position => omega
  have ordinary : allocation.type.bound = false := by
    cases position with
    | zero => simp [store] at found; cases found; rfl
    | succ position =>
        cases position with
        | zero => simp [store] at found; cases found; rfl
        | succ position =>
            cases position with
            | zero => simp [store] at found; cases found; rfl
            | succ position => omega
  have supported : position = 0 ∨ position = 1 ∨ position = 2 := by omega
  refine ⟨.term position, constant_decodes position inside, ?_, by simp [ordinary]⟩
  rw [sort]
  exact Preterm.HasType.term (declaration := termDeclaration) (by simp [signature, supported])

private theorem arities (term : Nat) (termDecl : TermDecl) (found : signature term = some termDecl) :
    Statements.arityOf terms term = some termDecl.arguments.length := by
  by_cases supported : term = 0 ∨ term = 1 ∨ term = 2
  · have same : termDeclaration = termDecl := by simpa [signature, supported] using found
    subst termDecl
    rcases supported with rfl | rfl | rfl <;> rfl
  · simp [signature, supported] at found

private theorem proof_zero : ProvenPointer signature (fun _ => none) theorems [] [] store 0 := by
  refine ⟨.term 0, 0, constant_decodes 0 (by decide), ?_, ?_⟩
  · exact Preterm.HasType.term (declaration := termDeclaration) (by rfl)
  · exact Derives.theoremApp (index := 0) (declaration := premiseDeclaration 0) (arguments := [])
      (instantiation := ⟨[], .term 0⟩) rfl
      ⟨(Substitution.checkAdmissible_iff signature [] [] []).mp (by decide), .nil, .term 0⟩ .nil

private theorem proof_one : ProvenPointer signature (fun _ => none) theorems [] [] store 1 := by
  refine ⟨.term 1, 0, constant_decodes 1 (by decide), ?_, ?_⟩
  · exact Preterm.HasType.term (declaration := termDeclaration) (by rfl)
  · exact Derives.theoremApp (index := 1) (declaration := premiseDeclaration 1) (arguments := [])
      (instantiation := ⟨[], .term 1⟩) rfl
      ⟨(Substitution.checkAdmissible_iff signature [] [] []).mp (by decide), .nil, .term 1⟩ .nil

/-- The two actual proof operands establish a different conclusion through
the decoded theorem's complete ordered premise list. -/
theorem two_actual_premises_prove_new_conclusion :
    Derives signature (fun _ => none) theorems [] [] (.term 2) := by
  have mainSound : StackSound signature (fun _ => none) theorems [] [] store before.main :=
    .proof proof_one (.proof proof_zero .empty)
  have admissible : Substitution.Admissible signature declaration.arguments [] [] :=
    (Substitution.checkAdmissible_iff signature declaration.arguments [] []).mp (by decide)
  have result := unify_theorem_proven signature (fun _ => none) theorems [] [] store typed terms entry declaration 2
    arities rfl rfl [] [] 2 before.main before.hyps after rfl rfl admissible mainSound rfl
  obtain ⟨expression, _, decoded, _, derived⟩ := result.1
  have same : expression = .term 2 := Option.some.inj (decoded.symm.trans (constant_decodes 2 (by decide)))
  subst expression
  exact derived

theorem reversed_actual_premises_refused :
    unifyRun store .apply { before with main := [.proof 0, .proof 1] } entry.unify = none := by decide

theorem expression_premise_refused :
    unifyStep store .apply ⟨[], [], [.expr 0], []⟩ .hyp = none := rfl

theorem pending_goal_premise_refused :
    unifyStep store .apply ⟨[], [], [.goal 0 0, .proof 0], []⟩ .hyp = none := rfl

theorem missing_actual_premise_refused :
    unifyRun store .apply { before with main := [.proof 1] } entry.unify = none := by decide

end Controls

end Mettapedia.Languages.MM0.MeTTa.MMBTheoremSoundness
