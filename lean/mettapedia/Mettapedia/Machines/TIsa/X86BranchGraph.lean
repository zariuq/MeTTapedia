import Mettapedia.Machines.TIsa.X86BranchRegion
import Mettapedia.GSLT.Meredith.GSLT

/-!
# Finite branch regions over the existing resource rewrite relation

Each source point owns one label and one native TEST/JZ body. Structural
admission checks the true fallthrough; the assembler checks named targets and
signed displacements. Source worlds and steps are those of CellEffects.profile.
The native entry records only readbacks for condition resources actually held.
The finite-path contracts cover branch bodies, including reflection from
fetched instruction pairs up to a declared region exit.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86BranchGraph
open _root_.X86Registers X86RegisterRefinement X86Execution X86Assembler
open X86BranchCompiler
local instance : MemoryPrimitives := X86Memory.ordinary
universe u
variable {Key : Type u}

def entryName (finish : Word) : List (Control.Branch Key) → Word
  | [] => finish
  | branch :: _ => branch.point

def sites (registers : Key → Fin 16) (branches : List (Control.Branch Key)) : List Chunk :=
  branches.flatMap fun branch => .label branch.point.toNat :: body branch (registers branch.condition)

def region (registers : Key → Fin 16) (finish : Word) (branches : List (Control.Branch Key)) : List Chunk :=
  sites registers branches ++ [.label finish.toNat]

def payload (registers : Key → Fin 16) (finish : Word) : List (Control.Branch Key) → List Chunk
  | [] => []
  | branch :: later => body branch (registers branch.condition) ++ region registers finish later

def code (registers : Key → Fin 16) (finish : Word) (branches : List (Control.Branch Key))
    (first tail : List Chunk) : List Chunk := first ++ (region registers finish branches ++ tail)

def Flows (finish : Word) : List (Control.Branch Key) → Prop
  | [] => True
  | branch :: later => branch.yes = entryName finish later ∧ Flows finish later

instance (finish : Word) (branches : List (Control.Branch Key)) : Decidable (Flows finish branches) := by
  induction branches with
  | nil => exact isTrue trivial
  | cons branch later ih => exact inferInstanceAs (Decidable (_ ∧ _))

def compile? (registers : Key → Fin 16) (activation : Nat) (finish : Word)
    (branches : List (Control.Branch Key)) (first tail : List Chunk) : Option Emission :=
  if Flows finish branches ∧ branches.all (fun branch => branch.activation == activation) = true then
    assemble (code registers finish branches first tail) else none

theorem compile?_iff (registers : Key → Fin 16) (activation : Nat) (finish : Word)
    (branches : List (Control.Branch Key)) (first tail : List Chunk) (emission : Emission) :
    compile? registers activation finish branches first tail = some emission ↔
      Flows finish branches ∧ (∀ branch ∈ branches, branch.activation = activation) ∧
      assemble (code registers finish branches first tail) = some emission := by
  unfold compile?
  by_cases valid : Flows finish branches ∧ branches.all (fun branch => branch.activation == activation) = true
  · rw [if_pos valid]
    have owners : ∀ branch ∈ branches, branch.activation = activation := by
      simpa only [List.all_eq_true,beq_iff_eq] using valid.2
    exact ⟨fun assembled => ⟨valid.1,owners,assembled⟩,fun accepted => accepted.2.2⟩
  · rw [if_neg valid]
    constructor
    · intro impossible; cases impossible
    · intro accepted
      exact False.elim (valid ⟨accepted.1,by simpa only [List.all_eq_true,beq_iff_eq] using accepted.2.1⟩)

theorem region_start (registers : Key → Fin 16) (finish : Word) (branches : List (Control.Branch Key)) :
    region registers finish branches =
      .label (entryName finish branches).toNat :: payload registers finish branches := by
  cases branches <;> simp [region,sites,entryName,payload,List.append_assoc]

theorem region_cons (registers : Key → Fin 16) (finish : Word) (branch : Control.Branch Key)
    (later : List (Control.Branch Key)) (flow : branch.yes = entryName finish later) :
    region registers finish (branch :: later) =
      lower branch (registers branch.condition) ++ payload registers finish later := by
  rw [region_start,entryName,payload,region_start,← flow]
  simp [lower,List.append_assoc]

theorem flows_at (finish : Word) (earlier : List (Control.Branch Key)) (branch : Control.Branch Key)
    (later : List (Control.Branch Key)) (valid : Flows finish (earlier ++ branch :: later)) :
    branch.yes = entryName finish later := by
  induction earlier with
  | nil => exact valid.1
  | cons head rest ih => exact ih valid.2

structure Layout (registers : Key → Fin 16) (activation : Nat) (finish : Word)
    (branches : List (Control.Branch Key)) (first tail : List Chunk) (emission : Emission) where
  flows : Flows finish branches
  owners : ∀ branch ∈ branches, branch.activation = activation
  labels : Labels
  resolved : labelsAt 0 (code registers finish branches first tail) = some labels
  assembled : assemble (code registers finish branches first tail) = some emission

theorem ofAssembly (registers : Key → Fin 16) (activation : Nat) (finish : Word)
    (branches : List (Control.Branch Key)) (first tail : List Chunk) (emission : Emission)
    (flows : Flows finish branches) (owners : ∀ branch ∈ branches, branch.activation = activation)
    (assembled : assemble (code registers finish branches first tail) = some emission) :
    Nonempty (Layout registers activation finish branches first tail emission) := by
  cases resolved : labelsAt 0 (code registers finish branches first tail) with
  | none => simp [assemble,resolved] at assembled
  | some labels => exact ⟨⟨flows,owners,labels,resolved,assembled⟩⟩

theorem ofCompilation (registers : Key → Fin 16) (activation : Nat) (finish : Word)
    (branches : List (Control.Branch Key)) (first tail : List Chunk) (emission : Emission)
    (accepted : compile? registers activation finish branches first tail = some emission) :
    Nonempty (Layout registers activation finish branches first tail emission) := by
  obtain ⟨flows,owners,assembled⟩ := (compile?_iff registers activation finish branches first tail emission).mp accepted
  exact ofAssembly registers activation finish branches first tail emission flows owners assembled

theorem Layout.site {registers : Key → Fin 16} {activation : Nat} {finish : Word}
    {branches : List (Control.Branch Key)} {first tail : List Chunk} {emission : Emission}
    (layout : Layout registers activation finish branches first tail emission)
    (branch : Control.Branch Key) (member : branch ∈ branches) :
    ∃ leading remaining, ∃ compiled : X86BranchCompiler.Compilation branch (registers branch.condition) leading remaining emission,
      compiled.labels = layout.labels := by
  obtain ⟨earlier,later,shape⟩ := List.mem_iff_append.mp member
  have flow : branch.yes = entryName finish later := by
    apply flows_at finish earlier branch later
    rw [← shape]
    exact layout.flows
  have whole : code registers finish branches first tail =
      (first ++ sites registers earlier) ++
        (lower branch (registers branch.condition) ++ (payload registers finish later ++ tail)) := by
    calc
      code registers finish branches first tail =
          first ++ (sites registers earlier ++ (region registers finish (branch :: later) ++ tail)) := by
        simp [code,shape,region,sites,List.flatMap_append,List.append_assoc]
      _ = _ := by rw [region_cons registers finish branch later flow]; simp [List.append_assoc]
  have assembled : assemble ((first ++ sites registers earlier) ++
      (lower branch (registers branch.condition) ++ (payload registers finish later ++ tail))) = some emission := by
    rw [← whole]
    exact layout.assembled
  obtain ⟨compiled⟩ := X86BranchCompiler.ofAssembly branch (registers branch.condition)
    (first ++ sites registers earlier) (payload registers finish later ++ tail) emission assembled
  refine ⟨_,_,compiled,?_⟩
  have resolved := layout.resolved
  rw [whole] at resolved
  exact Option.some.inj (compiled.resolved.symm.trans resolved)

structure Ready {registers : Key → Fin 16} {activation : Nat} {finish : Word}
    {branches : List (Control.Branch Key)} {first tail : List Chunk} {emission : Emission}
    (layout : Layout registers activation finish branches first tail emission)
    (base : Int) (keys : Finset (Control.Location Key)) (values : Control.Location Key → Word) (native : State) where
  origin : X86LegacyFetch.Basis native
  lower : -(2 ^ 47 : Int) ≤ base
  upper : base + (emission.bytes.length : Nat) + 3 < (2 ^ 47 : Int)
  offset : Nat
  control : X86Assembler.lookup layout.labels (values (.inl activation)).toNat = some offset
  location : origin.address.toInt = base + (offset : Nat)
  loaded : X86CodePlacement.Placed native base (view emission.bytes)
  reads : ∀ branch ∈ branches, .inr branch.condition ∈ keys →
    X86RegisterRefinement.lookup native (registers branch.condition) = some (values (.inr branch.condition))
  flags : BitVec 32
  flagsKnown : native.regs.get? .rflags = some flags
  quiet : native.regs.get? .log_register_writes = some false

section Execution
variable [DecidableEq Key]
variable (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
variable {registers : Key → Fin 16} {activation : Nat} {finish : Word}
variable {branches : List (Control.Branch Key)} {first tail : List Chunk} {emission : Emission}
variable (layout : Layout registers activation finish branches first tail emission)
variable {base : Int} {keys : Finset (Control.Location Key)}

omit [DecidableEq Key] in
theorem Ready.pointer {values : Control.Location Key → Word} {native : State}
    (ready : Ready layout base keys values native) :
    native.regs.get? .rip = some ((address base ready.offset).signExtend 64) := by
  have actual : address base ready.offset = ready.origin.address := by
    unfold address
    rw [← ready.location]
    exact BitVec.ofInt_toInt
  rw [actual]
  exact ready.origin.rip

def Ready.revalue {values : Control.Location Key → Word} {native : State}
    (ready : Ready layout base keys values native) (nextValues : Control.Location Key → Word)
    (controlPresent : .inl activation ∈ keys)
    (agree : ∀ location ∈ keys, values location = nextValues location) :
    Ready layout base keys nextValues native := {
  ready with
  control := by rw [← agree (.inl activation) controlPresent]; exact ready.control
  reads := by
    intro branch member present
    rw [← agree (.inr branch.condition) present]
    exact ready.reads branch member present }

theorem advance (values : Control.Location Key → Word) (native : State)
    (ready : Ready layout base keys values native) (branch : Control.Branch Key) (member : branch ∈ branches)
    (included : branch.recipe.support ⊆ keys) (current : values (.inl activation) = branch.point)
    (canonical : values (.inr branch.condition) = 0 ∨ values (.inr branch.condition) = 1) :
    letI : OtherOpcodeHandlers := X86BranchGate.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, ∃ _next : Ready layout base keys
        (Function.update values (.inl activation) (chosen branch (values (.inr branch.condition)))) after,
      (CellEffects.profile (branches.map Control.Branch.recipe)).theory.rewrites (Cells.encode keys values)
        (Cells.encode keys (Function.update values (.inl activation) (chosen branch (values (.inr branch.condition))))) ∧
      (X86FuelPrefix.fetches 2).run native = .ok () after ∧
      RegisterFrame X86BranchGate.writes native after ∧ X86ControlFlags.Preserved native after ∧
      ∀ count ≤ 2, ∀ observed, (X86FuelPrefix.fetches count).run native = .ok () observed →
        RegisterFrame X86BranchGate.writes native observed := by
  let : OtherOpcodeHandlers := X86BranchGate.handlers other extra
  let : VectorOpcodeHandlers := vector
  have owner := layout.owners branch member
  have conditionPresent : .inr branch.condition ∈ keys :=
    included (by simp [CellEffects.Recipe.support,Control.Branch.recipe])
  obtain ⟨leading,remaining,compiled,sameLabels⟩ := layout.site branch member
  have position : ready.offset = width leading := by
    have resolved := ready.control
    rw [current,← sameLabels] at resolved
    exact Option.some.inj (resolved.symm.trans compiled.point)
  let entry : Entry (registers branch.condition) (width leading) emission native := {
    base := base
    origin := ready.origin
    lower := ready.lower
    upper := ready.upper
    location := by rw [← position]; exact ready.location
    loaded := ready.loaded
    value := values (.inr branch.condition)
    known := ready.reads branch member conditionPresent
    flags := ready.flags
    flagsKnown := ready.flagsKnown
    quiet := ready.quiet }
  obtain ⟨after,correct⟩ := X86BranchCompiler.realizes_compiled other extra vector branch
    (registers branch.condition) leading remaining emission compiled native entry keys values included
    (by rw [owner]; exact current) rfl canonical
  have source := X86BranchRegion.source_in correct (branches.map Control.Branch.recipe)
    (List.mem_map.mpr ⟨branch,member,rfl⟩)
  have sourceNamed : (CellEffects.profile (branches.map Control.Branch.recipe)).theory.rewrites
      (Cells.encode keys values)
      (Cells.encode keys (Function.update values (.inl activation) (chosen branch (values (.inr branch.condition))))) := by
    simpa only [entry,owner] using source
  obtain ⟨resumed,sameBase,_sameValue⟩ := correct.next_entry (registers branch.condition)
    (values (.inr branch.condition)) entry.known
  have baseEq : resumed.base = base := sameBase
  refine ⟨after,{
    origin := resumed.origin
    lower := ready.lower
    upper := ready.upper
    offset := chosenOffset compiled entry.value
    control := ?_
    location := ?_
    loaded := correct.image
    reads := ?_
    flags := resumed.flags
    flagsKnown := resumed.flagsKnown
    quiet := resumed.quiet },sourceNamed,correct.run,correct.frame,correct.control,correct.prefixes⟩
  · rw [Function.update_self,← sameLabels]
    exact correct.outputLabel
  · rw [← baseEq]
    exact resumed.location
  · intro nextBranch nextMember present
    have framed := correct.frame.lookup (registers nextBranch.condition)
      (by generalize registers nextBranch.condition = register; fin_cases register <;> decide)
    rw [framed,Function.update_of_ne (by simp)]
    exact ready.reads nextBranch nextMember present

theorem realizes_step (values : Control.Location Key → Word) (native : State)
    (ready : Ready layout base keys values native) (following : Multiset (Cells.Cell (Control.Location Key)))
    (source : (CellEffects.profile (branches.map Control.Branch.recipe)).theory.rewrites
      (Cells.encode keys values) following) :
    letI : OtherOpcodeHandlers := X86BranchGate.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ nextValues after, ∃ _next : Ready layout base keys nextValues after,
      following = Cells.encode keys nextValues ∧
      (X86FuelPrefix.fetches 2).run native = .ok () after ∧
      RegisterFrame X86BranchGate.writes native after ∧ X86ControlFlags.Preserved native after ∧
      ∀ count ≤ 2, ∀ observed, (X86FuelPrefix.fetches count).run native = .ok () observed →
        RegisterFrame X86BranchGate.writes native observed := by
  let : OtherOpcodeHandlers := X86BranchGate.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨recipe,member,written,included,guarded,endpoint⟩ :=
    (CellEffects.profile_rewrite_iff (branches.map Control.Branch.recipe) keys values following).mp source
  obtain ⟨branch,present,rfl⟩ := List.mem_map.mp member
  obtain ⟨current,target⟩ := (branch.guard_iff values written).mp guarded
  have owner := layout.owners branch present
  have possibilities := (branch.target?_iff _ _).mp target
  have canonical : values (.inr branch.condition) = 0 ∨ values (.inr branch.condition) = 1 :=
    possibilities.imp And.left And.left
  have chosenEq : written (.inl branch.activation) = chosen branch (values (.inr branch.condition)) := by
    rcases possibilities with ⟨zero,result⟩ | ⟨one,result⟩
    · have zero' : values (.inr branch.condition) = (0#64) := zero
      unfold chosen
      rw [if_pos zero']
      exact result
    · have nonzero : values (.inr branch.condition) ≠ (0#64) := by rw [one]; decide
      unfold chosen
      rw [if_neg nonzero]
      exact result
  rw [branch.overwrite_eq,chosenEq,owner] at endpoint
  obtain ⟨after,next,_step,run,frame,control,prefixes⟩ :=
    advance other extra vector layout values native ready branch present included
      (by rw [← owner]; exact current) canonical
  exact ⟨_,after,next,endpoint,run,frame,control,prefixes⟩

theorem reflects_step (values : Control.Location Key → Word) (native observed : State)
    (ready : Ready layout base keys values native) (branch : Control.Branch Key) (member : branch ∈ branches)
    (included : branch.recipe.support ⊆ keys) (current : values (.inl activation) = branch.point)
    (canonical : values (.inr branch.condition) = 0 ∨ values (.inr branch.condition) = 1)
    (candidate : letI : OtherOpcodeHandlers := X86BranchGate.handlers other extra
      letI : VectorOpcodeHandlers := vector
      (X86FuelPrefix.fetches 2).run native = .ok () observed) :
    ∃ _next : Ready layout base keys
        (Function.update values (.inl activation) (chosen branch (values (.inr branch.condition)))) observed,
      (CellEffects.profile (branches.map Control.Branch.recipe)).theory.rewrites (Cells.encode keys values)
        (Cells.encode keys (Function.update values (.inl activation) (chosen branch (values (.inr branch.condition))))) ∧
      RegisterFrame X86BranchGate.writes native observed ∧ X86ControlFlags.Preserved native observed := by
  let : OtherOpcodeHandlers := X86BranchGate.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after,next,source,run,frame,control,_prefixes⟩ :=
    advance other extra vector layout values native ready branch member included current canonical
  have same := X86FuelPrefix.fetches_deterministic 2 native after observed run candidate
  subst observed
  exact ⟨next,source,frame,control⟩

theorem prefixes_join [OtherOpcodeHandlers] [VectorOpcodeHandlers]
    (writes : Finset Register) (firstCount secondCount : Nat) (before middle : State)
    (firstRun : (X86FuelPrefix.fetches firstCount).run before = .ok () middle)
    (firstPrefixes : ∀ count ≤ firstCount, ∀ observed,
      (X86FuelPrefix.fetches count).run before = .ok () observed → RegisterFrame writes before observed)
    (secondPrefixes : ∀ count ≤ secondCount, ∀ observed,
      (X86FuelPrefix.fetches count).run middle = .ok () observed → RegisterFrame writes middle observed) :
    ∀ count ≤ firstCount + secondCount, ∀ observed,
      (X86FuelPrefix.fetches count).run before = .ok () observed → RegisterFrame writes before observed := by
  intro count within observed candidate
  by_cases early : count ≤ firstCount
  · exact firstPrefixes count early observed candidate
  · have total : count = firstCount + (count - firstCount) := by omega
    rw [total] at candidate
    obtain ⟨intermediate,firstPart,rest⟩ :=
      X86BlockCompiler.fetches_split firstCount (count - firstCount) before observed candidate
    have same := X86FuelPrefix.fetches_deterministic firstCount before middle intermediate firstRun firstPart
    subst intermediate
    exact ((firstPrefixes firstCount (by omega) middle firstRun).trans
      (secondPrefixes (count - firstCount) (by omega) observed rest)).mono (by simp)

/-- Lists record actual source rewrites, retaining repeated states and the exact path length. -/
theorem realizes_path (values : Control.Location Key → Word) (native : State)
    (ready : Ready layout base keys values native)
    (visited : List (Multiset (Cells.Cell (Control.Location Key))))
    (source : List.IsChain (CellEffects.profile (branches.map Control.Branch.recipe)).theory.rewrites
      (Cells.encode keys values :: visited)) :
    letI : OtherOpcodeHandlers := X86BranchGate.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ nextValues after, ∃ _next : Ready layout base keys nextValues after,
      Cells.encode keys nextValues = visited.getLastD (Cells.encode keys values) ∧
      (X86FuelPrefix.fetches (2 * visited.length)).run native = .ok () after ∧
      RegisterFrame X86BranchGate.writes native after ∧ X86ControlFlags.Preserved native after ∧
      ∀ count ≤ 2 * visited.length, ∀ observed,
        (X86FuelPrefix.fetches count).run native = .ok () observed →
          RegisterFrame X86BranchGate.writes native observed := by
  let : OtherOpcodeHandlers := X86BranchGate.handlers other extra
  let : VectorOpcodeHandlers := vector
  induction visited generalizing values native with
  | nil =>
    refine ⟨values,native,ready,rfl,X86FuelPrefix.fetches_zero native,
      RegisterFrame.refl _ _,X86ControlFlags.Preserved.refl native,?_⟩
    intro count within observed candidate
    have zero : count = 0 := by simpa using within
    subst count
    have same := X86FuelPrefix.fetches_deterministic 0 native native observed
      (X86FuelPrefix.fetches_zero native) candidate
    subst observed
    exact RegisterFrame.refl _ _
  | cons nextSource later ih =>
    obtain ⟨firstStep,restSource⟩ := List.isChain_cons_cons.mp source
    obtain ⟨middleValues,middle,middleReady,sourceEq,firstRun,firstFrame,firstControl,firstPrefixes⟩ :=
      realizes_step other extra vector layout values native ready nextSource firstStep
    have remaining : List.IsChain (CellEffects.profile (branches.map Control.Branch.recipe)).theory.rewrites
        (Cells.encode keys middleValues :: later) := by rw [← sourceEq]; exact restSource
    obtain ⟨lastValues,after,lastReady,endpoint,restRun,restFrame,restControl,restPrefixes⟩ :=
      ih middleValues middle middleReady remaining
    have full := X86FuelPrefix.fetches_then 2 (2 * later.length) native middle after firstRun restRun
    have prefixes := prefixes_join X86BranchGate.writes 2 (2 * later.length) native middle
      firstRun firstPrefixes restPrefixes
    have countEq : 2 * (nextSource :: later).length = 2 + 2 * later.length := by simp [Nat.mul_add,Nat.add_comm]
    rw [← countEq] at full prefixes
    refine ⟨lastValues,after,lastReady,?_,full,(firstFrame.trans restFrame).mono (by simp),
      firstControl.trans restControl,prefixes⟩
    rw [List.getLastD_cons,sourceEq]
    exact endpoint

theorem reflects_path (values : Control.Location Key → Word) (native observed : State)
    (ready : Ready layout base keys values native)
    (visited : List (Multiset (Cells.Cell (Control.Location Key))))
    (source : List.IsChain (CellEffects.profile (branches.map Control.Branch.recipe)).theory.rewrites
      (Cells.encode keys values :: visited))
    (candidate : letI : OtherOpcodeHandlers := X86BranchGate.handlers other extra
      letI : VectorOpcodeHandlers := vector
      (X86FuelPrefix.fetches (2 * visited.length)).run native = .ok () observed) :
    ∃ nextValues, ∃ _next : Ready layout base keys nextValues observed,
      Cells.encode keys nextValues = visited.getLastD (Cells.encode keys values) ∧
      RegisterFrame X86BranchGate.writes native observed ∧ X86ControlFlags.Preserved native observed := by
  let : OtherOpcodeHandlers := X86BranchGate.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨nextValues,after,next,endpoint,run,frame,control,_prefixes⟩ :=
    realizes_path other extra vector layout values native ready visited source
  have same := X86FuelPrefix.fetches_deterministic (2 * visited.length) native after observed run candidate
  subst observed
  exact ⟨nextValues,next,endpoint,frame,control⟩

/-- A declared exit is observed at its resolved native address. -/
def AtExit (labels : Labels) (base : Int) (exits : List Word) (native : State) : Prop :=
  ∃ label ∈ exits, ∃ offset, X86Assembler.lookup labels label.toNat = some offset ∧
    native.regs.get? .rip = some ((address base offset).signExtend 64)

/-- Every exit resolves to an address distinct from each interior branch. -/
def checkExitOffsets (labels : Labels) (interior exits : List Word) : Bool :=
  exits.all fun label => match X86Assembler.lookup labels label.toNat with
    | none => false
    | some offset => interior.all fun point => X86Assembler.lookup labels point.toNat != some offset

omit [DecidableEq Key] in
theorem Ready.exit_iff {values : Control.Location Key → Word} {native : State}
    (ready : Ready layout base keys values native) (exits : List Word)
    (named : values (.inl activation) ∈ exits ∨ values (.inl activation) ∈ branches.map Control.Branch.point)
    (checked : checkExitOffsets layout.labels (branches.map Control.Branch.point) exits = true) :
    AtExit layout.labels base exits native ↔ values (.inl activation) ∈ exits := by
  constructor
  · rintro ⟨label,admitted,offset,found,pointer⟩
    rcases named with done | point
    · exact done
    have length := (assemble_correct _ _ layout.assembled).1
    have within {name pos : Nat} (hit : X86Assembler.lookup layout.labels name = some pos) :
        pos ≤ emission.bytes.length := by
      have bound := (labels_inside 0 _ _ layout.resolved _ (lookup_member _ _ _ hit)).2
      simpa only [Nat.zero_add,← length] using bound
    have upper : base + (emission.bytes.length : Nat) < (2 ^ 47 : Int) := by have := ready.upper; omega
    have exitInt := address_toInt base ready.lower upper offset (within found)
    have currentInt := address_toInt base ready.lower upper ready.offset (within ready.control)
    have bits := Option.some.inj ((Ready.pointer layout ready).symm.trans pointer)
    have coordinates := congrArg BitVec.toInt bits
    rw [BitVec.toInt_signExtend_of_le (by decide : 48 ≤ 64),
      BitVec.toInt_signExtend_of_le (by decide : 48 ≤ 64),currentInt,exitInt] at coordinates
    have equal : ready.offset = offset := by omega
    have rule := List.all_eq_true.mp checked label admitted
    change (match X86Assembler.lookup layout.labels label.toNat with
      | none => false
      | some offset => (branches.map Control.Branch.point).all
          fun point => X86Assembler.lookup layout.labels point.toNat != some offset) = true at rule
    rw [found] at rule
    have distinct := List.all_eq_true.mp rule _ point
    rw [ready.control,equal] at distinct
    simp at distinct
  · intro done
    exact ⟨_,done,ready.offset,ready.control,Ready.pointer layout ready⟩

/-- Recover the source path from the native run and its instruction count.
Each completed pair before the last one must still be inside the region. -/
theorem reflect_native_run (exits : List Word)
    (targets : ∀ branch ∈ branches,
      (branch.yes ∈ exits ∨ branch.yes ∈ branches.map Control.Branch.point) ∧
      (branch.no ∈ exits ∨ branch.no ∈ branches.map Control.Branch.point))
    (resources : ∀ branch ∈ branches, branch.recipe.support ⊆ keys)
    (values : Control.Location Key → Word) (native observed : State)
    (ready : Ready layout base keys values native)
    (initial : values (.inl activation) ∈ exits ∨ values (.inl activation) ∈ branches.map Control.Branch.point)
    (canonical : ∀ branch ∈ branches, values (.inr branch.condition) = 0 ∨ values (.inr branch.condition) = 1)
    (count : Nat)
    (run : letI : OtherOpcodeHandlers := X86BranchGate.handlers other extra
      letI : VectorOpcodeHandlers := vector
      (X86FuelPrefix.fetches (2 * count)).run native = .ok () observed)
    (inside : letI : OtherOpcodeHandlers := X86BranchGate.handlers other extra
      letI : VectorOpcodeHandlers := vector
      ∀ prefixCount < count, ∀ state, (X86FuelPrefix.fetches (2 * prefixCount)).run native = .ok () state →
        ¬ AtExit layout.labels base exits state) :
    letI : OtherOpcodeHandlers := X86BranchGate.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ finalValues, ∃ _entry : Ready layout base keys finalValues observed,
      ∃ visited : List (Multiset (Cells.Cell (Control.Location Key))),
        List.IsChain (CellEffects.profile (branches.map Control.Branch.recipe)).theory.rewrites
          (Cells.encode keys values :: visited) ∧
        visited.length = count ∧
        Cells.encode keys finalValues = visited.getLastD (Cells.encode keys values) ∧
        (finalValues (.inl activation) ∈ exits ∨ finalValues (.inl activation) ∈ branches.map Control.Branch.point) ∧
        RegisterFrame X86BranchGate.writes native observed ∧ X86ControlFlags.Preserved native observed ∧
        ∀ prefixCount ≤ 2 * count, ∀ state, (X86FuelPrefix.fetches prefixCount).run native = .ok () state →
          RegisterFrame X86BranchGate.writes native state := by
  let : OtherOpcodeHandlers := X86BranchGate.handlers other extra
  let : VectorOpcodeHandlers := vector
  induction count generalizing values native with
  | zero =>
    have result := X86FuelPrefix.fetches_deterministic 0 native native observed
      (X86FuelPrefix.fetches_zero native) (by simpa only [Nat.mul_zero] using run)
    subst observed
    refine ⟨values,ready,[],.singleton _,rfl,rfl,initial,RegisterFrame.refl _ _,
      X86ControlFlags.Preserved.refl native,?_⟩
    intro prefixCount within state step
    have zero : prefixCount = 0 := by omega
    subst prefixCount
    have result := X86FuelPrefix.fetches_deterministic 0 native native state (X86FuelPrefix.fetches_zero native) step
    subst state
    exact RegisterFrame.refl _ _
  | succ count ih =>
    have named : values (.inl activation) ∈ branches.map Control.Branch.point := by
      rcases initial with atExit | atBranch
      · exfalso
        apply inside 0 (Nat.zero_lt_succ _) native
        · exact X86FuelPrefix.fetches_zero native
        · exact ⟨_,atExit,ready.offset,ready.control,Ready.pointer layout ready⟩
      · exact atBranch
    obtain ⟨branch,member,current⟩ := List.mem_map.mp named
    obtain ⟨firstAfter,firstReady,source,firstRun,firstFrame,firstFlags,firstPrefixes⟩ :=
      advance other extra vector layout values native ready branch member (resources branch member)
        current.symm (canonical branch member)
    have partition : 2 * (count + 1) = 2 + 2 * count := by omega
    obtain ⟨middle,middleRun,rest⟩ := X86BlockCompiler.fetches_split 2 (2 * count) native observed
      (partition ▸ run)
    have same := X86FuelPrefix.fetches_deterministic 2 native firstAfter middle firstRun middleRun
    subst middle
    let nextValues := Function.update values (.inl activation) (chosen branch (values (.inr branch.condition)))
    have nextInitial : nextValues (.inl activation) ∈ exits ∨
        nextValues (.inl activation) ∈ branches.map Control.Branch.point := by
      simp only [nextValues,Function.update_self,chosen]
      split
      · exact (targets branch member).2
      · exact (targets branch member).1
    have nextCanonical : ∀ branch ∈ branches,
        nextValues (.inr branch.condition) = 0 ∨ nextValues (.inr branch.condition) = 1 := by
      intro nextBranch present
      simpa only [nextValues,Function.update_of_ne (by simp : .inr nextBranch.condition ≠ (.inl activation : Control.Location Key))]
        using canonical nextBranch present
    have nextInside : ∀ prefixCount < count, ∀ state,
        (X86FuelPrefix.fetches (2 * prefixCount)).run firstAfter = .ok () state →
          ¬ AtExit layout.labels base exits state := by
      intro prefixCount bound state part
      have combined := X86FuelPrefix.fetches_then 2 (2 * prefixCount) native firstAfter state firstRun part
      apply inside (prefixCount + 1) (by omega) state
      have size : 2 * (prefixCount + 1) = 2 + 2 * prefixCount := by omega
      rw [size]
      exact combined
    obtain ⟨following,entry,visited,path,length,endpoint,atName,frame,flags,prefixes⟩ :=
      ih nextValues firstAfter firstReady nextInitial nextCanonical rest nextInside
    refine ⟨following,entry,Cells.encode keys nextValues :: visited,List.isChain_cons_cons.mpr ⟨source,path⟩,
      by simp [length],by simpa only [List.getLastD_cons] using endpoint,atName,
      (firstFrame.trans frame).mono (by simp),firstFlags.trans flags,?_⟩
    rw [partition]
    exact prefixes_join X86BranchGate.writes 2 (2 * count) native firstAfter firstRun firstPrefixes prefixes

theorem source_path_iff (before following : Multiset (Cells.Cell (Control.Location Key))) :
    (CellEffects.profile (branches.map Control.Branch.recipe)).theory.MultiStep before following ↔
      ∃ visited, List.IsChain (CellEffects.profile (branches.map Control.Branch.recipe)).theory.rewrites
        (before :: visited) ∧ visited.getLastD before = following := by
  refine (Mettapedia.GSLT.Meredith.multiStep_iff_reflTransGen
    (CellEffects.profile (branches.map Control.Branch.recipe)).theory before following).trans ?_
  constructor
  · intro source
    obtain ⟨visited,path,endpoint⟩ := List.exists_isChain_cons_of_relationReflTransGen source
    exact ⟨visited,path,by cases visited <;> exact endpoint⟩
  · rintro ⟨visited,path,endpoint⟩
    exact List.relationReflTransGen_of_exists_isChain_cons visited path
      (by cases visited <;> exact endpoint)

theorem realizes_multistep (values : Control.Location Key → Word) (native : State)
    (ready : Ready layout base keys values native) (following : Multiset (Cells.Cell (Control.Location Key)))
    (source : (CellEffects.profile (branches.map Control.Branch.recipe)).theory.MultiStep
      (Cells.encode keys values) following) :
    letI : OtherOpcodeHandlers := X86BranchGate.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ count nextValues after, ∃ _next : Ready layout base keys nextValues after,
      following = Cells.encode keys nextValues ∧
      (X86FuelPrefix.fetches (2 * count)).run native = .ok () after ∧
      RegisterFrame X86BranchGate.writes native after ∧ X86ControlFlags.Preserved native after ∧
      ∀ prefixCount ≤ 2 * count, ∀ observed,
        (X86FuelPrefix.fetches prefixCount).run native = .ok () observed →
          RegisterFrame X86BranchGate.writes native observed := by
  let : OtherOpcodeHandlers := X86BranchGate.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨visited,path,endpoint⟩ := (source_path_iff _ _).mp source
  obtain ⟨nextValues,after,next,represented,run,frame,control,prefixes⟩ :=
    realizes_path other extra vector layout values native ready visited path
  exact ⟨visited.length,nextValues,after,next,endpoint.symm.trans represented.symm,run,frame,control,prefixes⟩

end Execution

#print axioms reflect_native_run
#print axioms Ready.exit_iff
end Mettapedia.Machines.TIsa.X86BranchGraph
