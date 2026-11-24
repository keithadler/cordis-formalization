import Cordis.Repairs.GuardedHistory
import Cordis.MediatedRegistryFrames
import Cordis.Renaming

/-! The grammar of a stored remaining iterator follows from actual Begin
and Iter steps. Its component is the one admitted at its registry birth. -/
namespace Cordis.Repairs.GuardedIteratorProvenance
open Calculus Stages GuardedHistory IncarnationReplay

universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
local notation "K" => Component Key Code
local notation "C" => Capture Name Key Value
local notation "Program" => Code → Instruction Name Key Value Code Error
variable {program : Code → Instruction Name Key Value Code Error}

abbrev Mediated (program : Program) (component : K) :=
  MediatedRegistry.Mediated program (fun key => component.requires key = true) (fun key => component.provides key = true)

def Entries (program : Program) (state : R) : Prop :=
  ∀ name row, state name = some row → Mediated program row.component row.component.entry

def NewEntries (program : Program) (before after : R) : Prop :=
  ∀ name row, before name = none → after name = some row → Mediated program row.component row.component.entry

omit [DecidableEq Name] [DecidableEq Key] in
theorem entries_after {before after : R} (stable : Frame.Stable before after)
    (earlier : Entries program before) (born : NewEntries program before after) : Entries program after := by
  intro name row found
  cases present : before name with
  | none => exact born name row present found
  | some original => exact (stable name original row present found).1 ▸ earlier name original present

private def current (row : F) : Option (K × Code) :=
  match row.phase with
  | .reloading code _ _ => some (row.component, code)
  | _ => none

private def currentAt (state : R) (name : Name) : Option (K × Code) := (state name).bind current

def Remaining (program : Program) (state : R) : Prop :=
  ∀ name component code, currentAt state name = some (component, code) → Mediated program component code

omit [DecidableEq Name] [DecidableEq Key] in
theorem Remaining.at_row {state : R} (stored : Remaining program state) {actor : Name} {row : F}
    (present : state actor = some row) {code : Code} {word : List (Inverse Name Key Value)} {view : View Name Key}
    (phase : row.phase = .reloading code word view) : Mediated program row.component code := by
  exact stored actor row.component code (by simp [currentAt, current, present, phase])

omit [DecidableEq Name] [DecidableEq Key] in
theorem Remaining.of_rows {state : R} (stored : ∀ actor row code word view, state actor = some row →
    row.phase = .reloading code word view → Mediated program row.component code) : Remaining program state := by
  intro actor component code found
  cases present : state actor with
  | none => simp [currentAt, present] at found
  | some row =>
    cases phase : row.phase <;> simp [currentAt, current, present, phase] at found
    obtain ⟨rfl, rfl⟩ := found
    exact stored actor row _ _ _ present phase

omit [DecidableEq Key] in
private theorem current_modify (state : R) (actor : Name) (change : F → F)
    (same : ∀ row, current (change row) = current row) :
    currentAt (Calculus.modify state actor change) = currentAt state := by
  funext name
  by_cases acts : name = actor
  · subst name
    cases present : state actor <;> simp [currentAt, Calculus.modify, present, same]
  · simp [currentAt, Calculus.modify, acts]

private theorem current_land {before after : R} {actor : Name} {code : Code}
    {token : Inverse Name Key Value} {next : Option Code} (landed : Land program actor code before after token next)
    (ready : Remaining program before) : Remaining program after := by
  cases landed with
  | unit => exact ready
  | provide state name code row key value action found declared empty =>
    have same : currentAt (write before actor key (some value)) = currentAt before :=
      current_modify _ _ _ (fun _ => rfl)
    intro n c x h
    rw [same] at h
    exact ready n c x h
  | operate state name code key call owner input output inverse reply action located returned =>
    have same : currentAt (write before owner key (some output)) = currentAt before :=
      current_modify _ _ _ (fun _ => rfl)
    intro n c x h
    rw [same] at h
    exact ready n c x h
  | instantiate state name code component child action guard =>
    intro n c x h
    by_cases same : n = child
    · subst n
      simp [currentAt, current, put, fresh] at h
    · exact ready n c x (by simpa [currentAt, put, same] using h)

private theorem current_capture (live : Name → Option Nat) (capture : C) (state : R) :
    currentAt (capture.apply live state) = currentAt state := by
  rcases capture with ⟨token, index⟩
  cases token with
  | unit => rfl
  | restrict | operate => exact current_modify _ _ _ (fun _ => rfl)
  | retire child =>
    simp only [Capture.apply]
    split
    · exact current_modify _ _ _ (fun _ => rfl)
    · rfl

private theorem current_replay (live : Name → Option Nat) (word : List C) (state : R) :
    currentAt (replay live word state) = currentAt state := by
  induction word generalizing state with
  | nil => rfl
  | cons head tail ih => exact (ih (head.apply live state)).trans (current_capture live head state)

private theorem current_discharge (word : List (Inverse Name Key Value)) (state : R) :
    currentAt (discharge Stages.undo word state) = currentAt state := by
  induction word generalizing state with
  | nil => rfl
  | cons head tail ih =>
    have kept : currentAt (Stages.undo head state) = currentAt state := by
      cases head with
      | unit => rfl
      | restrict | operate | retire => exact current_modify _ _ _ (fun _ => rfl)
    exact (ih (Stages.undo head state)).trans kept

omit [DecidableEq Key] in
private theorem remaining_mark {state : R} (ready : Remaining program state) (actor : Name)
    (phase : Phase Name Key Code (Inverse Name Key Value))
    (selected : ∀ row component code, state actor = some row →
      current ({ row with phase := phase } : F) = some (component, code) → Mediated program component code) :
    Remaining program (mark state actor phase) := by
  intro name component code found
  by_cases acts : name = actor
  · subst name
    cases present : state actor with
    | none => simp [currentAt, mark, Calculus.modify, present] at found
    | some row => exact selected row component code present (by simpa [currentAt, mark, Calculus.modify, present] using found)
  · exact ready name component code (by simpa [currentAt, mark, Calculus.modify, acts] using found)

omit [DecidableEq Name] [DecidableEq Key] in
private theorem selected_mediated {component : K} {code next : Code} {reply : Outcome Name Value}
    (grammar : Mediated program component code) (chosen : (program code).next reply = some next) :
    Mediated program component next := by
  cases grammar with
  | unit _ _ terminal => rw [terminal] at chosen; cases chosen
  | operation _ _ _ _ _ tails | provision _ _ _ _ _ tails | birth _ _ _ tails => exact tails _ _ chosen

theorem remaining_after_native {rule : Labeled.Rule} {actor : Name} {before after : R}
    (step : Labeled.Step program rule actor before after) (entries : Entries program before)
    (stored : Remaining program before) : Remaining program after := by
  cases step with
  | insert state name component parent ready =>
    intro n c code h
    by_cases same : n = actor
    · subst n; simp [currentAt, current, put, fresh] at h
    · exact stored n c code (by simpa [currentAt, put, same] using h)
  | retire state name present =>
    have same : currentAt (Calculus.retire before actor) = currentAt before := current_modify _ _ _ (fun _ => rfl)
    intro n c code h
    rw [same] at h
    exact stored n c code h
  | remove state name ready =>
    intro n c code h
    by_cases same : n = actor
    · subst n; simp [currentAt, erase] at h
    · exact stored n c code (by simpa [currentAt, erase, same] using h)
  | begin state name row view present phase free target =>
    refine remaining_mark stored actor _ ?_
    intro other payload code found same
    cases Option.some.inj (present.symm.trans found)
    cases Option.some.inj same
    exact entries actor row present
  | iter state middle name row code stack view inverse following present phase target landed =>
    refine remaining_mark (current_land landed stored) actor _ ?_
    intro other payload next found same
    cases Option.some.inj same
    have declaration := (Frame.land_stable program landed actor row other present found).1
    obtain ⟨reply, _, selected⟩ := Renaming.land_has_outcome program landed
    exact declaration ▸ selected_mediated (stored.at_row present phase) selected
  | finish _ _ name _ _ _ _ _ present phase target landed =>
    exact remaining_mark (current_land landed stored) actor _ (fun _ _ _ _ h => Option.noConfusion h)
  | divert _ _ name _ _ _ _ _ present phase stale split =>
    rcases split with ⟨rfl, _⟩ | ⟨_, _, landed, _⟩
    · exact remaining_mark stored actor _ (fun _ _ _ _ h => Option.noConfusion h)
    · exact remaining_mark (current_land landed stored) actor _ (fun _ _ _ _ h => Option.noConfusion h)
  | leave _ name _ _ _ present phase stale =>
    exact remaining_mark stored actor _ (fun _ _ _ _ h => Option.noConfusion h)
  | unload state name _ word _ present phase free =>
    apply remaining_mark _ actor _ (fun _ _ _ _ h => Option.noConfusion h)
    intro n c code h
    rw [current_discharge] at h
    exact stored n c code h

theorem remaining_after_guarded {before after : R} {notes : Vestigial.CutNotes Name Key Value}
    {event : LegalHistory.Event Name Key Code} (step : GuardedSuffix.Transition program notes event before after)
    (entries : Entries program before) (stored : Remaining program before) : Remaining program after := by
  rcases transition_cases step with native | ⟨actor, _, unload⟩
  · exact remaining_after_native native entries stored
  · obtain ⟨_, _, _, _, _, rfl⟩ := unload
    apply remaining_mark _ actor _ (fun _ _ _ _ h => Option.noConfusion h)
    intro name payload code h
    rw [current_replay] at h
    exact stored name payload code h

/-- Only components actually introduced by the history require a grammar
at admission. Every later stored field inherits it through real steps. -/
def BirthsMediated {last : Nat} (trace : Trace program last) : Prop :=
  ∀ time, time < last → NewEntries program (trace.state time) (trace.state (time + 1))

theorem codes_at_cut {last : Nat} (trace : Trace program last) (admitted : BirthsMediated trace)
    (time : Nat) (bounded : time ≤ last) : Entries program (trace.state time) ∧ Remaining program (trace.state time) := by
  induction time with
  | zero => rw [trace.start]; exact ⟨fun _ _ h => Option.noConfusion h, fun _ _ _ h => Option.noConfusion h⟩
  | succ time ih =>
    have earlier := ih (by omega)
    have step := (trace.step time (by omega : time < last)).1
    exact ⟨entries_after (transition_stable step) earlier.1 (admitted time (by omega)),
      remaining_after_guarded step earlier.1 earlier.2⟩

end Cordis.Repairs.GuardedIteratorProvenance
