import Cordis.Repairs.ReplayBindingDomains

/-! The partial reading of Definition 58 for every actual guarded step.
The state application is the chosen primitive or guarded saved-word replay.
Its result is followed by the rule's table-preserving control edit. -/
namespace Cordis.Repairs.GuardedPartialApplications
open Calculus Stages StageRecovery GuardedHistory LegalHistory
open IncarnationReplay (Capture replay)
open ReplayBindingDomains (WordDefined saved_word_defined saved_subword_slot)
open PartialReplayRegistry (Coeffects projectApplication)
open Vestigial (CutNotes eventActor)
open RuleEvaluation (Use Edit TablesUnchanged)

universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "Notes" => CutNotes Name Key Value
local notation "Ev" => Event Name Key Code
local notation "U" => Use Name Key Value Code
local notation "E" => Edit Name Key Value Code
variable {program : Code → Instruction Name Key Value Code Error}

/-- The captured word for an unload belongs to the source cut. Its
application requires every intermediate partial inverse to be defined. -/
def Application (meaning : Coeffects program) (notes : Notes) (actor : Name)
    (use : U) (before after : R) : Prop :=
  match use with
  | .accumulator tokens =>
    tokens = (notes.2 actor).map Capture.token ∧ WordDefined meaning notes.1 (notes.2 actor) before ∧
      after = replay notes.1 (notes.2 actor) before
  | _ => RuleEvaluation.Application program actor use before after

/-- Equation (53) with partial slot applications and the guarded word.
The witness comes from the actual rule, including the chosen fresh draw. -/
def Factored (meaning : Coeffects program) (notes : Notes) (event : Ev) (before after : R) : Prop :=
  ∃ (use : U) (middle : R) (edit : E),
    Application meaning notes (eventActor event) use before middle ∧
    use.allowed (eventRule event) before (eventActor event) ∧
    edit.allowed (eventRule event) (eventActor event) ∧ edit.valid middle ∧ after = edit.apply middle ∧
    TablesUnchanged middle after ∧
    ∀ owner key, projectApplication meaning before (eventActor event) use owner key (tableAt before owner key) =
      some (tableAt middle owner key)

private theorem native_factorization (meaning : Coeffects program) {event : Ev} {before after : R} {notes : Notes}
    (native : Labeled.Step program (eventRule event) (eventActor event) before after)
    (ordinary : eventRule event ≠ .unload) :
    Factored meaning notes event before after := by
  obtain ⟨use, middle, edit, applied, selected, edited, valid, output, tables⟩ :=
    RuleEvaluation.step_factorization program native
  refine ⟨use, middle, edit, ?_, selected, edited, valid, output, tables, ?_⟩
  · cases applied with
    | identity => exact .identity _
    | iteration _ _ _ _ _ land => exact .iteration _ _ _ _ _ land
    | accumulator => exact False.elim (ordinary selected.1)
  · intro owner key
    cases applied with
    | identity => rfl
    | iteration _ _ _ _ _ land => exact PartialReplayRegistry.projectApplication_landing meaning land owner key
    | accumulator => exact False.elim (ordinary selected.1)

/-- An actual or counterfactual unload factors whenever its guarded rule
and every partial inverse in the selected word have been established. -/
theorem unload_factorization (meaning : Coeffects program) {before after : R} {notes : Notes} {actor : Name}
    (step : GuardedSuffix.Unload actor before notes after)
    (defined : WordDefined meaning notes.1 (notes.2 actor) before) :
    Factored meaning notes (.lifecycle .unload actor) before after := by
  obtain ⟨row, view, present, phase, free, endpoint⟩ := step
  let word := notes.2 actor
  let middle := replay notes.1 word before
  refine ⟨.accumulator (word.map Capture.token), middle, .phase actor .inactive,
    ⟨rfl, defined, rfl⟩, ⟨rfl, row, view, present, phase⟩,
    by simp [Edit.allowed, eventRule, eventActor, Lifecycle.rule], trivial, endpoint, ?_, ?_⟩
  · rw [endpoint]
    exact (Edit.phase actor .inactive).preserves_tables middle trivial
  · exact WordDefined.slot_projection meaning notes.1 word before defined

theorem transition_factorization (meaning : Coeffects program) {notes : Notes} {event : Ev} {before after : R}
    (step : GuardedSuffix.Transition program notes event before after)
    (unloadDefined : ∀ actor, event = .lifecycle .unload actor → WordDefined meaning notes.1 (notes.2 actor) before) :
    Factored meaning notes event before after := by
  cases event with
  | command command =>
    exact native_factorization meaning (ExchangeReplay.command_labeled command step)
      (by cases command <;> simp [eventRule, ExchangeReplay.commandRule])
  | lifecycle kind actor =>
    cases kind
    case unload => exact unload_factorization meaning step (unloadDefined actor rfl)
    all_goals exact native_factorization meaning step (by simp [eventRule, Lifecycle.rule])

/-- Every guarded rule has its actual partial application and control edit.
Each intermediate inverse domain in the unload case follows from its trace. -/
theorem trace_factorization {last : Nat} (trace : Trace program last) (meaning : Coeffects program)
    {time : Nat} (bounded : time < last) :
    Factored meaning (trace.notes time) (trace.event time) (trace.state time) (trace.state (time + 1)) :=
  transition_factorization meaning (trace.step time bounded).1
    (fun actor _ => saved_word_defined trace time (Nat.le_of_lt bounded) meaning actor)

theorem factorization_of_step {last : Nat} (trace : Trace program last) (meaning : Coeffects program)
    {time : Nat} (bounded : time ≤ last) {event : Ev} {after : R} {recorded : Notes}
    (step : GuardedSuffix.Step program event (time + 1) (trace.state time) (trace.notes time) after recorded) :
    Factored meaning (trace.notes time) event (trace.state time) after := by
  have factored := trace_factorization (trace.extendAt bounded step) meaning (Nat.lt_succ_self time)
  simpa [Trace.extendAt, show ¬ time + 1 ≤ time by omega] using factored

end Cordis.Repairs.GuardedPartialApplications
