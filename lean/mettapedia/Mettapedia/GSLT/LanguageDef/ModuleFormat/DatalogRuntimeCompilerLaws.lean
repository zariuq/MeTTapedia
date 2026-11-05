import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogRuntimeCompiler

/-! Laws of the actual in-process source/Space adapter. Capturing occurrences
is compositional and retains first errors. Set closure and publication are
separate observations, rather than identifications made by the input reader. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogRuntimeCompiler

open Mettapedia.Languages.Datalog
private abbrev HostAtom := Mettapedia.Languages.MeTTa.OSLFCore.Atom

example : forceIntegerBounds 0 = true := by decide +kernel

theorem hostNamesValid_injective (separator : String) (program : Program)
    (valid : hostNamesValid separator program = true) (first second : QualifiedName)
    (memFirst : first ∈ (ProgramStatic.declarations program).map (·.name))
    (memSecond : second ∈ (ProgramStatic.declarations program).map (·.name))
    (same : String.intercalate separator first = String.intercalate separator second) :
    first = second := by
  have pair := List.all_eq_true.mp (List.all_eq_true.mp valid first memFirst) second memSecond
  simpa [same] using pair

theorem hostValue_typed (type : AttributeType) (host : HostAtom) (value : Mettapedia.Languages.Datalog.Value)
    (read : hostValue type host = some value) : StaticTyping.ValueTyped value type := by
  cases host with
  | grounded ground =>
    cases ground <;> cases type <;>
      simp_all [hostValue, StaticTyping.ValueTyped, Mettapedia.Languages.Datalog.Value.type, Mettapedia.Languages.Datalog.Value.fits64]
    · rcases read with ⟨bounds, rfl⟩
      simpa using bounds
    · rcases read with ⟨bounds, rfl⟩
      simp
      omega
    · cases read
      simp
  | symbol name => cases type <;> simp [hostValue] at read
  | var name => cases type <;> simp [hostValue] at read
  | expression children => cases type <;> simp [hostValue] at read

/-- Concatenation preserves successful captures and the same first failure.
In particular, splitting a snapshot cannot alter which malformed input is
reported or turn duplicate occurrences into one input occurrence. -/
theorem capture_append (separator : String) (program : Program) (first second : List HostAtom) :
    capture separator program (first ++ second) = (do
      let left ← capture separator program first
      let right ← capture separator program second
      pure (left ++ right)) := by
  exact Mettapedia.Machines.SelectiveRowCapture.collect_append (captureRow separator program) first second

theorem capture_preserves_duplicates (separator : String) (program : Program)
    (rows : List HostAtom) (facts : List GroundFact)
    (read : capture separator program rows = .ok facts) :
    capture separator program (rows ++ rows) = .ok (facts ++ facts) := by
  rw [capture_append, read]
  rfl

/-- Component admission binds an independently supplied package to the
actual authored components; mismatched semantics cannot inherit execution. -/
theorem bindComponents_exact (expected supplied bound : Components) (compiler : Value) :
    bindComponents expected supplied compiler = .ok bound ↔
      compilerCompatible compiler = true ∧ supplied = expected ∧ bound = expected := by
  unfold bindComponents
  split
  next accepted =>
    have condition : compilerCompatible compiler = true ∧ supplied = expected := by
      simpa using accepted
    constructor
    · intro result
      exact ⟨condition.1, condition.2, (Except.ok.inj result).symm⟩
    · rintro ⟨_, _, rfl⟩
      rfl
  next refused =>
    constructor
    · intro impossible
      cases impossible
    · rintro ⟨compatible, same, _⟩
      simp [compatible, same] at refused

theorem verificationReply_verified (result : Option Bool) :
    verificationReply result = .ok (Lean.Json.mkObj [("status",.str "verified")]) ↔ result = some true := by
  cases result with
  | none =>
    constructor
    · intro same
      let status : Except String Lean.Json → Except String String := fun reply =>
        reply.bind fun value => value.getObjValAs? String "status"
      have conflict : ("pending" : String) = "verified" := Except.ok.inj (congrArg status same)
      exact False.elim ((by decide : ("pending" : String) ≠ "verified") conflict)
    · intro impossible
      cases impossible
  | some value =>
    cases value with
    | false => constructor <;> intro impossible <;> cases impossible
    | true => constructor <;> intro _ <;> rfl

/-- The actual provider's successful reply discharges both checks. Neither
a caller's flag nor a native recognizer outcome is a verification receipt. -/
theorem verifySource_verified (source packet forest identity allowance : String)
    (accepted : verifySource source packet forest identity allowance =
      .ok (Lean.Json.mkObj [("status",.str "verified")])) :
    ∃ evidence, readSourceEvidence packet forest identity allowance = .ok evidence ∧
      SourceSyntaxForest.complete? verificationSpec source evidence.forest evidence.identity evidence.rounds = some true ∧
      SourceCatalogue.validate? verificationSpec SouffleDatalog.SourcePolicy.filters source
        evidence.forest evidence.identity evidence.packets evidence.rounds = some true := by
  unfold verifySource at accepted
  cases read : readSourceEvidence packet forest identity allowance with
  | error reason => rw [read] at accepted; cases accepted
  | ok evidence =>
    rw [read] at accepted
    change verificationReply (SourceCatalogueVerification.verify? verificationSpec SouffleDatalog.SourcePolicy.filters
      source evidence.forest evidence.identity evidence.packets evidence.rounds) = _ at accepted
    exact ⟨evidence, rfl, SourceCatalogueVerification.verify?_sound _ _ _ _ _ _ _
      ((verificationReply_verified _).mp accepted)⟩

private def controlText : String := String.ofList ['a', Char.ofNat 0, 'b', '\r', '\n', '"', '\\']

-- Executable transport control: the library JSON compressor is opaque to
-- kernel reduction. This check is separate from the theorems above.
#guard Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics.readSource
    (CettaWireData.render (.string controlText)) =
      .ok [(.grounded (.string controlText) : HostAtom)]

private def colliding : Program := ⟨[
  .declaration ⟨["a:b"], []⟩,
  .declaration ⟨["a","b"], []⟩]⟩

example : hostNamesValid ":" colliding = false := by decide +kernel
example : hostNamesValid "." colliding = true := by decide +kernel
example : hostValue .number (.grounded (.int (2 ^ 63))) = none := by decide +kernel
example : hostValue .unsigned (.grounded (.int (2 ^ 64 - 1))) =
    some (.unsigned (2 ^ 64 - 1)) := by decide +kernel

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogRuntimeCompiler
