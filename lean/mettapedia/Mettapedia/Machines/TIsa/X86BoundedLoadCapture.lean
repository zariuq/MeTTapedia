import Mettapedia.Machines.TIsa.X86BoundedLoadSource
import Mettapedia.Machines.TIsa.X86AssemblerCapture

/-!
# Every ordinary LOAD site in the first thirteen native consumers

The source paths, complete bounds/MOV bytes and actual invalid-handler target
are checked together. Independent source-tree traversal proves coverage rather
than relying on the export's span count. Native observations then establish a
loaded reusable template and its branch geometry at any valid image placement.
-/

set_option autoImplicit false
set_option Elab.async false
namespace Mettapedia.Machines.TIsa.X86BoundedLoadCapture
open _root_.X86Registers X86RegisterRefinement X86Execution X86BoundedLoad

def loadPaths : P1Source.Stmt → List (List Nat)
  | .instruction (.load ..) => [[]]
  | .seq first second => (loadPaths first).map (0 :: ·) ++ (loadPaths second).map (1 :: ·)
  | .branch _ yes no => (loadPaths yes).map (1 :: ·) ++ (loadPaths no).map (2 :: ·)
  | .counted _ _ _ body | .early _ _ _ _ body => (loadPaths body).map (0 :: ·)
  | _ => []


def decode? (program : P1Capture.Program) (span : P1Capture.Span) : Option Instruction := do
  let path ← span.path
  let statement ← program.source.body.atPath path
  match statement with
  | .instruction source =>
      if span.offset ≤ X86AssemblerCapture.invalidAt program then X86BoundedLoadSource.lower? source (X86AssemblerCapture.invalidAt program - span.offset) else none
  | _ => none

def Valid (program : P1Capture.Program) (span : P1Capture.Span) (instruction : Instruction) : Prop :=
  span.offset + (bytes instruction).length ≤ program.size ∧ span.length = (bytes instruction).length ∧
  span.offset + instruction.reject = X86AssemblerCapture.invalidAt program ∧
  (X86Bounds.branchDelta (layout instruction) 23).toInt = (instruction.reject : Int) - 23 ∧
  (X86Bounds.branchDelta (layout instruction) (X86Bounds.compareAt (layout instruction))).toInt =
    (instruction.reject : Int) - X86Bounds.compareAt (layout instruction) ∧
  (X86Bounds.branchDelta (layout instruction) (X86Bounds.exitAt (layout instruction))).toInt =
    (instruction.reject : Int) - X86Bounds.exitAt (layout instruction)

instance (program : P1Capture.Program) (span : P1Capture.Span) (instruction : Instruction) :
    Decidable (Valid program span instruction) := inferInstanceAs (Decidable (_ ∧ _))

def bytesMatch (span : P1Capture.Span) (instruction : Instruction) (view : NativeImage.View) : Bool :=
  (List.finRange span.length).all fun index =>
    view.read (span.offset + index.val) == ((bytes instruction)[index.val]?).map (BitVec.ofNat 8)

def matchesOn (program : P1Capture.Program) (span : P1Capture.Span) (view : NativeImage.View) : Bool :=
  match decode? program span with
  | none => false
  | some instruction => decide (Valid program span instruction) && bytesMatch span instruction view

def siteMatches (program : P1Capture.Program) (span : P1Capture.Span) : Bool := matchesOn program span program.view

noncomputable def sites : List (P1Capture.Program × P1Capture.Span) :=
  (ImportedP1.programs.take 13).flatMap fun program =>
    (program.spans.filter fun span => span.kind == "LOAD").map fun span => (program,span)

def covered (program : P1Capture.Program) : Bool :=
  ((program.spans.filter fun span => span.kind == "LOAD").mapM P1Capture.Span.path) == some (loadPaths program.source.body)

theorem site_count : sites.length = 125 := by kernel_reflexivity
def programCheck (program : P1Capture.Program) : Bool :=
  (program.spans.filter fun span => span.kind == "LOAD").all (siteMatches program)

theorem all_programs_checked : (ImportedP1.programs.take 13).all programCheck = true := by kernel_reflexivity

theorem all_checked : sites.all (fun site => siteMatches site.1 site.2) = true := by
  simp only [sites,List.all_flatMap,List.all_map,Function.comp_def]
  exact all_programs_checked
theorem all_covered : (ImportedP1.programs.take 13).all covered = true := by kernel_reflexivity

theorem source_coverage (program : P1Capture.Program) (member : program ∈ ImportedP1.programs.take 13) :
    (program.spans.filter fun span => span.kind == "LOAD").mapM P1Capture.Span.path = some (loadPaths program.source.body) :=
  beq_iff_eq.mp (List.all_eq_true.mp all_covered program member)

theorem decoded_source (program : P1Capture.Program) (span : P1Capture.Span) (instruction : Instruction)
    (decoded : decode? program span = some instruction) :
    ∃ path, span.path = some path ∧ program.source.body.atPath path = some (.instruction (X86BoundedLoadSource.p1 instruction)) := by
  unfold decode? at decoded
  obtain ⟨path,pathFound,following⟩ := Option.bind_eq_some_iff.mp decoded
  obtain ⟨statement,statementFound,built⟩ := Option.bind_eq_some_iff.mp following
  cases statement <;> try contradiction
  case instruction source =>
    change (if span.offset ≤ X86AssemblerCapture.invalidAt program then
      X86BoundedLoadSource.lower? source (X86AssemblerCapture.invalidAt program - span.offset) else none) = some instruction at built
    by_cases before : span.offset ≤ X86AssemblerCapture.invalidAt program
    · rw [if_pos before] at built
      exact ⟨path,pathFound,by rw [X86BoundedLoadSource.lower?_source built];exact statementFound⟩
    · simp only [if_neg before] at built
      cases built

theorem matched_info (program : P1Capture.Program) (span : P1Capture.Span) (instruction : Instruction)
    (decoded : decode? program span = some instruction) (checked : siteMatches program span = true) :
    Valid program span instruction ∧ ∀ index : Fin span.length,
      program.view.read (span.offset + index.val) = ((bytes instruction)[index.val]?).map (BitVec.ofNat 8) := by
  simp only [siteMatches,matchesOn,decoded,Bool.and_eq_true,decide_eq_true_eq] at checked
  refine ⟨checked.1,?_⟩
  intro index
  exact beq_iff_eq.mp (List.all_eq_true.mp checked.2 index (by simp))

theorem captured_site (program : P1Capture.Program) (span : P1Capture.Span) (member : (program,span) ∈ sites) :
    ∃ instruction, decode? program span = some instruction ∧ Valid program span instruction ∧
      ∀ index : Fin span.length,
        program.view.read (span.offset + index.val) = ((bytes instruction)[index.val]?).map (BitVec.ofNat 8) := by
  have checked := List.all_eq_true.mp all_checked (program,span) member
  cases decoded : decode? program span with
  | none => simp [siteMatches,matchesOn,decoded] at checked
  | some instruction => exact ⟨instruction,rfl,matched_info program span instruction decoded checked⟩

/-- Every captured site rejects to the invalid-input entry `mov eax, 3` of its own image. -/
theorem reject_targets_invalid (program : P1Capture.Program) (span : P1Capture.Span) (member : (program,span) ∈ sites) :
    ∃ instruction, decode? program span = some instruction ∧
      program.view.read (span.offset + instruction.reject) = some (0xb8#8) ∧
      program.view.read (span.offset + instruction.reject + 1) = some (3#8) := by
  obtain ⟨instruction,decoded,valid,_⟩ := captured_site program span member
  have imported : program ∈ ImportedP1.programs := by
    obtain ⟨source,inSource,inSpans⟩ := List.mem_flatMap.mp member
    obtain ⟨_,_,same⟩ := List.mem_map.mp inSpans
    cases same
    exact List.mem_of_mem_take inSource
  have entry := X86AssemblerCapture.all_invalid_entries program imported
  rw [← valid.2.2.1] at entry
  exact ⟨instruction,decoded,entry⟩

theorem loaded_template (program : P1Capture.Program) (span : P1Capture.Span) (instruction : Instruction)
    (decoded : decode? program span = some instruction) (checked : siteMatches program span = true)
    (native : State) (base : Int) (origin : X86LegacyFetch.Basis native)
    (placed : origin.address.toInt = base + span.offset)
    (loaded : X86P1LoadCapture.Loaded program native base) :
    codeLoaded native origin.address.toInt (bytes instruction) := by
  obtain ⟨valid,encoded⟩ := matched_info program span instruction decoded checked
  intro index byte present
  have inside : index < span.length := by have := (List.getElem?_eq_some_iff.mp present).1;rw [valid.2.1];exact this
  have read := encoded ⟨index,inside⟩
  rw [present,Option.map_some] at read
  have shifted : address base (span.offset + index) = address origin.address.toInt index := by
    rw [placed]
    simp only [address,Int.natCast_add,Int.add_assoc]
  simpa only [shifted] using (loaded (span.offset + index) (by have := valid.1;have := valid.2.1;omega)).trans read

def geometry (program : P1Capture.Program) (span : P1Capture.Span) (instruction : Instruction)
    (valid : Valid program span instruction) (start : BitVec 48) (base : Int)
    (placed : start.toInt = base + span.offset) (upper : base + program.size + 3 < (2 ^ 47 : Int)) :
    X86Bounds.Context (layout instruction) start where
  extent := program.size + 3 - span.offset
  upper := by have := valid.1;rw [placed];omega
  codeWithin := by have := valid.1;rw [bytes_length] at this;omega
  rejectWithin := by
    change instruction.reject ≤ program.size + 3 - span.offset
    have := valid.2.2.1
    have small : X86AssemblerCapture.invalidAt program ≤ program.size := Nat.sub_le _ _
    omega
  overflowDelta := valid.2.2.2.1
  shortDelta := valid.2.2.2.2.1
  rangeDelta := valid.2.2.2.2.2

theorem geometry_tail (program : P1Capture.Program) (span : P1Capture.Span) (instruction : Instruction)
    (valid : Valid program span instruction) (start : BitVec 48) (base : Int)
    (placed : start.toInt = base + span.offset) (upper : base + program.size + 3 < (2 ^ 47 : Int)) :
    X86Bounds.exitAt (layout instruction) + 10 ≤ (geometry program span instruction valid start base placed upper).extent := by
  change X86Bounds.exitAt (layout instruction) + 10 ≤ program.size + 3 - span.offset
  have := valid.1
  rw [bytes_length] at this
  omega

namespace Controls
private noncomputable def firstSite : P1Capture.Program × P1Capture.Span := sites[0]'(by rw [site_count];decide)
private def firstInstruction : Instruction := ⟨false,6,1,0,⟨0,by decide⟩,752,by decide,by decide,by decide⟩

theorem first_decoded : decode? firstSite.1 firstSite.2 = some firstInstruction := by kernel_reflexivity

theorem changed_branch_target_rejected :
    bytesMatch firstSite.2 { firstInstruction with reject := 753 } firstSite.1.view = false := by kernel_reflexivity

private noncomputable def changedOpcode : NativeImage.View := {
  firstSite.1.view with read := fun offset =>
    if offset = firstSite.2.offset + 37 then some (0x8d#8) else firstSite.1.view.read offset }

theorem changed_load_opcode_rejected : matchesOn firstSite.1 firstSite.2 changedOpcode = false := by kernel_reflexivity

theorem frame_destination_declines :
    (X86BoundedLoadSource.lower? (.load .u64 .word64 0 0 1 0) 256).isNone = true := by decide

theorem negative_offset_declines :
    (X86BoundedLoadSource.lower? (.load .u64 .word64 0 6 1 (-1#32)) 256).isNone = true := by decide
end Controls

#print axioms all_checked
#print axioms all_covered
#print axioms decoded_source
#print axioms loaded_template
#print axioms Controls.changed_branch_target_rejected
#print axioms Controls.changed_load_opcode_rejected
end Mettapedia.Machines.TIsa.X86BoundedLoadCapture
