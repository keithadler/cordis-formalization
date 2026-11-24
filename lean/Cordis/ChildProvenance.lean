import Cordis.Orchestration
import Cordis.Frame
import Cordis.Progress
import Cordis.EntangledApplications

/-! Definition74's child provenance is derived from actual captured retirement,
not imposed as a lifecycle guard. Every nonretired nonroot child remains named
in its parent's current accumulator. Consequently a quiet state's live children
have active parents, the missing middle clause in Lemma77's proof. -/
namespace Cordis.ChildProvenance
open Calculus Stages
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
variable [DecidableEq Name] [DecidableEq Key]
set_option linter.unusedSectionVars false

def Pending (r : R) (debt : Name → List (Inverse Name Key Value)) : Prop :=
  ∀ child entry parent, r child = some entry → entry.parent = some parent → entry.retired = false →
    ∃ owner, r parent = some owner ∧ .retire child ∈ debt parent ++ owner.phase.accumulator

def Captured (r : R) : Prop := Pending r (fun _ => [])

theorem captured_empty : Captured (fun _ => none : R) := by
  intro child entry parent impossible
  cases impossible

theorem captured_pending (r : R) (debt : Name → List (Inverse Name Key Value)) (old : Captured r) :
    Pending r debt := by
  intro child entry parent present ancestor live
  obtain ⟨owner, found, member⟩ := old child entry parent present ancestor live
  exact ⟨owner, found, List.mem_append_right _ (by simpa using member)⟩

theorem false_of_monotone {before after : Bool} (mono : before = true → after = true)
    (live : after = false) : before = false := by
  cases before <;> cases after <;> simp_all

theorem modify_pending (r : R) (actor : Name) (change : F → F)
    (debt : Name → List (Inverse Name Key Value)) (old : Pending r debt)
    (parent : ∀ f, (change f).parent = f.parent)
    (accumulator : ∀ f, (change f).phase.accumulator = f.phase.accumulator)
    (retired : ∀ f, f.retired = true → (change f).retired = true) :
    Pending (Calculus.modify r actor change) debt := by
  have origins : ∀ child entry, Calculus.modify r actor change child = some entry →
      ∃ original, r child = some original ∧ entry.parent = original.parent ∧
        (entry.retired = false → original.retired = false) := by
    intro child entry present
    by_cases same : child = actor
    · subst child
      cases before : r actor with
      | none => simp [Calculus.modify, before] at present
      | some original =>
        have same : change original = entry := Option.some.inj (by simpa [Calculus.modify, before] using present)
        subst entry
        exact ⟨original, rfl, parent original, false_of_monotone (retired original)⟩
    · exact ⟨entry, by simpa [Calculus.modify, same] using present, rfl, id⟩
  intro child entry ancestor present hp live
  obtain ⟨original, found, ancestry, wasLive⟩ := origins child entry present
  obtain ⟨owner, ownerFound, member⟩ := old child original ancestor found (ancestry.symm.trans hp) (wasLive live)
  by_cases same : ancestor = actor
  · subst ancestor
    exact ⟨change owner, by simp [Calculus.modify, ownerFound], by simpa [accumulator] using member⟩
  · exact ⟨owner, by simp [Calculus.modify, same, ownerFound], member⟩

theorem write_pending (r : R) (actor : Name) (key : Key) (value : Option Value)
    (debt : Name → List (Inverse Name Key Value)) (old : Pending r debt) :
    Pending (write r actor key value) debt :=
  modify_pending r actor _ debt old (fun _ => rfl) (fun _ => rfl) (fun _ h => h)

theorem retire_pending (r : R) (actor : Name) (debt : Name → List (Inverse Name Key Value))
    (old : Pending r debt) : Pending (Calculus.retire r actor) debt :=
  modify_pending r actor _ debt old (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)

theorem undo_pending (r : R) (inverse : Inverse Name Key Value)
    (debt : Name → List (Inverse Name Key Value)) (old : Pending r debt) :
    Pending (Stages.undo inverse r) debt := by
  cases inverse with
  | unit => exact old
  | restrict => exact write_pending _ _ _ _ debt old
  | operate => exact modify_pending _ _ _ debt old (fun _ => rfl) (fun _ => rfl) (fun _ h => h)
  | retire => exact retire_pending _ _ debt old

theorem discharge_pending (r : R) (acc : List (Inverse Name Key Value))
    (debt : Name → List (Inverse Name Key Value)) (old : Pending r debt) :
    Pending (discharge Stages.undo acc r) debt := by
  induction acc generalizing r with
  | nil => exact old
  | cons inverse rest ih => exact ih _ (undo_pending r inverse debt old)

/-- Insertion creates a fresh empty accumulator. Existing children cannot have
pointed to the previously absent name because their captured owner existed. -/
theorem insert_pending (r : R) (child : Name) (component : Component Key Code) (parent : Option Name)
    (absent : r child = none) (debt : Name → List (Inverse Name Key Value)) (old : Pending r debt)
    (newChild : ∀ ancestor, parent = some ancestor →
      ∃ owner, r ancestor = some owner ∧ .retire child ∈ debt ancestor ++ owner.phase.accumulator) :
    Pending (put r child (fresh component parent)) debt := by
  intro name entry ancestor present hp live
  by_cases same : name = child
  · subst name
    have eq : (fresh component parent : F) = entry := Option.some.inj (by simpa [put] using present)
    subst entry
    obtain ⟨owner, found, member⟩ := newChild ancestor hp
    have different : ancestor ≠ child := by intro same; subst ancestor; simp [absent] at found
    exact ⟨owner, by simp [put, different, found], member⟩
  · have original : r name = some entry := by simpa [put, same] using present
    obtain ⟨owner, found, member⟩ := old name entry ancestor original hp live
    have different : ancestor ≠ child := by intro same; subst ancestor; simp [absent] at found
    exact ⟨owner, by simp [put, different, found], member⟩

theorem insert_root (r : R) (name : Name) (component : Component Key Code)
    (absent : r name = none) (old : Captured r) : Captured (put r name (fresh component none)) :=
  insert_pending r name component none absent _ old (fun _ impossible => nomatch impossible)

def owing (actor : Name) (inverses : List (Inverse Name Key Value)) (name : Name) : List (Inverse Name Key Value) :=
  if name = actor then inverses else []

/-- The real instantiation primitive supplies precisely the new child-retire
debt. Other primitives preserve captured debts and create no child. -/
theorem land_pending (program : Code → Instruction Name Key Value Code Error)
    {actor : Name} {code : Code} {r s : R} {inverse : Inverse Name Key Value} {next : Option Code}
    (land : Land program actor code r s inverse next) (old : Captured r) :
    Pending s (owing actor [inverse]) := by
  cases land with
  | unit => exact captured_pending _ _ old
  | provide => exact write_pending _ _ _ _ _ (captured_pending _ _ old)
  | operate => exact write_pending _ _ _ _ _ (captured_pending _ _ old)
  | instantiate r actor code component child action ready =>
    apply insert_pending r child component (some actor) ready.1 _ (captured_pending _ _ old)
    intro ancestor hp
    have same : ancestor = actor := Option.some.inj hp.symm
    subst ancestor
    have present := ready.2.1 actor rfl
    cases found : r actor with
    | none => exact False.elim (present found)
    | some owner => exact ⟨owner, rfl, by simp [owing]⟩

/-- Commit the pending retirement exactly where L-Iter/Finish/Divert pushes
the returned inverse. The parent activation's previous children stay captured. -/
theorem mark_capture (r : R) (actor : Name) (owner : F) (phase)
    (present : r actor = some owner) (extra : List (Inverse Name Key Value))
    (pending : Pending r (owing actor extra))
    (captures : phase.accumulator = extra ++ owner.phase.accumulator) :
    Captured (mark r actor phase) := by
  intro child entry ancestor found hp live
  have origins : ∃ original, r child = some original ∧ original.parent = entry.parent ∧ original.retired = entry.retired := by
    by_cases same : child = actor
    · subst child
      have eq : { owner with phase := phase } = entry := Option.some.inj (by simpa [mark, Calculus.modify, present] using found)
      subst entry
      exact ⟨owner, present, rfl, rfl⟩
    · exact ⟨entry, by simpa [mark, Calculus.modify, same] using found, rfl, rfl⟩
  obtain ⟨original, originalFound, ancestry, retirement⟩ := origins
  obtain ⟨parent, parentFound, member⟩ := pending child original ancestor originalFound (ancestry.trans hp) (retirement.trans live)
  by_cases same : ancestor = actor
  · subst ancestor
    have eq : parent = owner := Option.some.inj (parentFound.symm.trans present)
    subst parent
    exact ⟨{ owner with phase := phase }, by simp [mark, Calculus.modify, present],
      by simpa [owing, captures] using member⟩
  · exact ⟨parent, by simp [mark, Calculus.modify, same, parentFound], by simpa [owing, same] using member⟩

/-- Every captured retirement is actually executed by LIFO discharge. Earlier
and later inverses cannot undo the monotone retirement flag. -/
theorem discharge_retires_member (r : R) (acc : List (Inverse Name Key Value))
    (child : Name) (before after : F) (present : r child = some before)
    (found : discharge Stages.undo acc r child = some after) (member : .retire child ∈ acc) :
    after.retired = true := by
  induction acc generalizing r before with
  | nil => simp at member
  | cons inverse rest ih =>
      rcases List.mem_cons.mp member with same | remaining
      · subst inverse
        have retiredFound : Stages.undo (.retire child) r child = some { before with retired := true } := by
          simp [Stages.undo, Calculus.retire, Calculus.modify, present]
        exact (Frame.discharge_stable (Stages.undo (.retire child) r) rest child _ after retiredFound found).2.2 rfl
      · obtain ⟨middle, middleFound, _⟩ := Ordering.undo_existing_phases r inverse child before present
        exact ih _ middle middleFound found remaining

theorem remove_captured (r : R) (actor : Name) (ready : Removable r actor) (old : Captured r) :
    Captured (erase r actor) := by
  intro child entry ancestor present hp live
  have different : child ≠ actor := by intro same; subst child; simp [erase] at present
  have before : r child = some entry := by simpa [erase, different] using present
  obtain ⟨owner, found, member⟩ := old child entry ancestor before hp live
  have parentDifferent : ancestor ≠ actor := by
    intro same
    subst ancestor
    simp only [Removable, found] at ready
    have noChildren := ready.2.2.2 child
    simp [before, hp] at noChildren
  exact ⟨owner, by simp [erase, parentDifferent, found], member⟩

/-- Resetting an accumulator is safe for the invariant only once every child
it owes has been retired. This side condition is proved from discharge below. -/
theorem mark_childless (r : R) (actor : Name) (owner : F) (phase)
    (present : r actor = some owner) (old : Captured r)
    (childless : ∀ child entry, r child = some entry → entry.parent = some actor → entry.retired = false → False) :
    Captured (mark r actor phase) := by
  intro child entry ancestor found hp live
  have origins : ∃ original, r child = some original ∧ original.parent = entry.parent ∧ original.retired = entry.retired := by
    by_cases same : child = actor
    · subst child
      have eq : { owner with phase := phase } = entry := Option.some.inj (by simpa [mark, Calculus.modify, present] using found)
      subst entry
      exact ⟨owner, present, rfl, rfl⟩
    · exact ⟨entry, by simpa [mark, Calculus.modify, same] using found, rfl, rfl⟩
  obtain ⟨original, originalFound, ancestry, retirement⟩ := origins
  have originalParent := ancestry.trans hp
  have originalLive := retirement.trans live
  obtain ⟨parent, parentFound, member⟩ := old child original ancestor originalFound originalParent originalLive
  have different : ancestor ≠ actor := by
    intro same
    subst ancestor
    exact childless child original originalFound originalParent originalLive
  exact ⟨parent, by simp [mark, Calculus.modify, different, parentFound], member⟩

theorem unload_captured (r : R) (actor : Name) (owner : F) (acc : List (Inverse Name Key Value))
    (view : View Name Key) (present : r actor = some owner) (unloading : owner.phase = .unloading acc view)
    (old : Captured r) : Captured (mark (discharge Stages.undo acc r) actor .inactive) := by
  obtain ⟨after, found, _⟩ := Ordering.discharge_existing_phases r acc actor owner present
  apply mark_childless _ actor after .inactive found (discharge_pending r acc _ old)
  intro child entry childFound parent live
  cases beforeFound : r child with
  | none =>
      have absent := EntangledApplications.discharge_preserves_absence acc r child beforeFound
      simp [absent] at childFound
  | some before =>
      have stable := Frame.discharge_stable r acc child before entry beforeFound childFound
      have oldParent : before.parent = some actor := stable.2.1.trans parent
      have oldLive : before.retired = false := false_of_monotone stable.2.2 live
      obtain ⟨parentEntry, parentFound, member⟩ := old child before actor beforeFound oldParent oldLive
      have same : parentEntry = owner := Option.some.inj (parentFound.symm.trans present)
      subst parentEntry
      have captured : .retire child ∈ acc := by simpa [unloading, Phase.accumulator] using member
      have retired := discharge_retires_member r acc child before entry beforeFound childFound captured
      cases live.symm.trans retired

theorem landing_mark_captured (program : Code → Instruction Name Key Value Code Error)
    {actor : Name} {code : Code} {r s : R} {inverse : Inverse Name Key Value} {next : Option Code}
    (land : Land program actor code r s inverse next) (owner : F) (present : r actor = some owner)
    (phase) (capture : phase.accumulator = inverse :: owner.phase.accumulator) (old : Captured r) :
    Captured (mark s actor phase) := by
  obtain ⟨entry, found, component, samePhase⟩ := Ordering.land_existing_control program land actor owner present
  apply mark_capture s actor entry phase found [inverse] (land_pending program land old)
  simpa [samePhase] using capture

/-- Captured-child provenance is preserved by every externally authorized rule,
including fresh child creation and both alternatives of L-Divert. -/
theorem step_captured (program : Code → Instruction Name Key Value Code Error)
    {r s : R} (step : Orchestration.Step program r s) (old : Captured r) : Captured s := by
  cases step with
  | insert name component ready => exact insert_root _ name component ready.1 old
  | retire name present => exact retire_pending _ name _ old
  | remove name ready => exact remove_captured _ name ready old
  | begin name fiber view present inactive free target =>
      exact mark_capture _ name fiber _ present [] (captured_pending _ _ old)
        (by simp [inactive, Phase.accumulator])
  | iter middle name fiber code acc view inverse next present reloading target landed =>
      exact landing_mark_captured program landed fiber present _ (by simp [reloading, Phase.accumulator]) old
  | finish middle name fiber code acc view inverse present reloading target landed =>
      exact landing_mark_captured program landed fiber present _ (by simp [reloading, Phase.accumulator]) old
  | divert middle name fiber code acc view tail present reloading stale alternative =>
      rcases alternative with ⟨rfl, rfl⟩ | ⟨inverse, next, landed, rfl⟩
      · exact mark_capture _ name fiber _ present [] (captured_pending _ _ old)
          (by simp [reloading, Phase.accumulator])
      · exact landing_mark_captured program landed fiber present _ (by simp [reloading, Phase.accumulator]) old
  | leave name fiber acc view present active stale =>
      exact mark_capture _ name fiber _ present [] (captured_pending _ _ old)
        (by simp [active, Phase.accumulator])
  | unload name fiber acc view present unloading guard => exact unload_captured _ name fiber acc view present unloading old

theorem reachable_captured (program : Code → Instruction Name Key Value Code Error)
    {r : R} (run : Orchestration.Run program (fun _ => none) r) : Captured r := by
  have preserves : ∀ {a b : R}, Orchestration.Run program a b → Captured a → Captured b := by
    intro a b path
    induction path with
    | refl => exact id
    | step previous step ih => exact fun old => step_captured program step (ih old)
  exact preserves run captured_empty

/-- At quiescence, a live child's captured retirement forces its parent
to be active. -/
theorem captured_quiet_parent_active {r : R} (captured : Captured r) (quiet : Progress.Quiet r)
    (child : Name) (entry : F) (parent : Name) (present : r child = some entry)
    (ancestor : entry.parent = some parent) (live : entry.retired = false) :
    ∃ owner, r parent = some owner ∧ owner.phase.available := by
  obtain ⟨owner, found, member⟩ := captured child entry parent present ancestor live
  have stable := quiet parent owner found
  cases phase : owner.phase with
  | inactive => simp [phase, Phase.accumulator] at member
  | reloading | unloading => simp [phase] at stable
  | active acc view => exact ⟨owner, found, by simp [phase, Phase.available]⟩

end Cordis.ChildProvenance
