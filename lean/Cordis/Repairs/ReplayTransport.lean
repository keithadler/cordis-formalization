import Cordis.Renaming
import Cordis.Repairs.IncarnationReplay

/-! Transport of actual captured words and incarnation-checked replay.
The correspondence of birth indices is explicit so that it can relate cuts
in histories whose steps have moved. -/
namespace Cordis.Repairs.IncarnationReplay
open Calculus Stages Incarnation
open PartialReplayRegistry (saved)
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "C" => Capture Name Key Value

def Capture.transport (p : Renaming.Permutation Name) (birth : Nat → Nat) (capture : C) : C :=
  ⟨Renaming.inverse p capture.token, birth capture.index⟩

def Capture.reindex (birth : Nat → Nat) (capture : C) : C :=
  { capture with index := birth capture.index }

private theorem reindex_matches {birth : Nat → Nat} (injective : Function.Injective birth)
    (live : Option Nat) (index : Nat) :
    live.map birth = some (birth index) ↔ live = some index := by
  cases live with
  | none => simp
  | some current =>
    exact ⟨fun h => congrArg some (injective (Option.some.inj h)),
      fun h => congrArg (Option.map birth) h⟩

/-- The transport of the instant at which a child was created must reflect as
well as preserve identity. Reordered histories need no monotonicity here. -/
theorem Capture.apply_transport [DecidableEq Name] [DecidableEq Key]
    (p : Renaming.Permutation Name) {birth : Nat → Nat} (injective : Function.Injective birth)
    {live other : Name → Option Nat}
    (paired : ∀ name, other (p.toFun name) = (live name).map birth)
    (capture : C) (state : R) :
    (capture.transport p birth).apply other (Renaming.registry p state) =
      Renaming.registry p (capture.apply live state) := by
  rcases capture with ⟨token, index⟩
  cases token with
  | retire child =>
    have guard : other (p.toFun child) = some (birth index) ↔ live child = some index := by
      rw [paired]
      exact reindex_matches injective _ _
    by_cases current : live child = some index <;>
      simp [Capture.transport, Capture.apply, Renaming.inverse, guard, current, Renaming.retire_eq]
  | unit => rfl
  | restrict owner key =>
    exact (Renaming.undo_eq p state (.restrict owner key)).symm
  | operate owner key inverse =>
    exact (Renaming.undo_eq p state (.operate owner key inverse)).symm

theorem replay_transport [DecidableEq Name] [DecidableEq Key]
    (p : Renaming.Permutation Name) {birth : Nat → Nat} (injective : Function.Injective birth)
    {live other : Name → Option Nat}
    (paired : ∀ name, other (p.toFun name) = (live name).map birth)
    (word : List C) (state : R) :
    replay other (word.map (Capture.transport p birth)) (Renaming.registry p state) =
      Renaming.registry p (replay live word state) := by
  induction word generalizing state with
  | nil => rfl
  | cons capture rest ih =>
    rw [List.map_cons, replay, replay, Capture.apply_transport p injective paired, ih]

theorem replay_reindex [DecidableEq Name] [DecidableEq Key]
    {birth : Nat → Nat} (injective : Function.Injective birth)
    {live other : Name → Option Nat} (paired : ∀ name, other name = (live name).map birth)
    (word : List C) (state : R) :
    replay other (word.map (Capture.reindex birth)) state = replay live word state := by
  have same (capture : C) (state : R) :
      (capture.reindex birth).apply other state = capture.apply live state := by
    rcases capture with ⟨token, index⟩
    cases token with
    | retire name => simp [Capture.reindex, Capture.apply, paired, reindex_matches injective]
    | _ => rfl
  induction word generalizing state with
  | nil => rfl
  | cons capture rest ih => rw [List.map_cons, replay, replay, same, ih]

variable [DecidableEq Name] in
theorem advance_annotate (index : Nat → Nat) {before after othBefore othAfter : R}
    {actor : Name} {time : Nat} {word otherWord : Name → List C}
    (earlier : ∀ name, otherWord name = (word name).map (Capture.reindex index))
    (source : saved othBefore actor = saved before actor)
    (target : saved othAfter actor = saved after actor) :
    ∀ name, advance othBefore othAfter actor (index time) otherWord name =
      (advance before after actor time word name).map (Capture.reindex index) := by
  intro name
  by_cases same : name = actor
  · subst name
    simp only [advance, source, target, earlier]
    cases saved after actor with
    | nil => rfl
    | cons token rest =>
      by_cases pushed : (saved before actor).length < rest.length + 1 <;>
        simp [pushed, Capture.reindex]
  · simp [advance, same, earlier]

/-- The live birth correspondence is automatic when the whole history is
renamed at the same indices, even if a name has been removed and reused. -/
theorem birthAt_renamed (p : Renaming.Permutation Name) (states : Nat → R)
    (name : Name) (time : Nat) :
    birthAt (fun index => Renaming.registry p (states index)) (p.toFun name) time =
      birthAt states name time := by
  induction time with
  | zero => cases seen : states 0 name <;> simp [birthAt, seen]
  | succ time ih =>
    simp only [birthAt, Renaming.registry_at, ih]
    cases states (time + 1) name <;> rfl

theorem replayAt_transport [DecidableEq Name] [DecidableEq Key]
    (p : Renaming.Permutation Name) {birth : Nat → Nat} (injective : Function.Injective birth)
    (states pairedStates : Nat → R) (time pairedTime : Nat)
    (related : pairedStates pairedTime = Renaming.registry p (states time))
    (paired : ∀ name, birthAt pairedStates (p.toFun name) pairedTime =
      (birthAt states name time).map birth)
    (word : List C) :
    replayAt pairedStates pairedTime (word.map (Capture.transport p birth)) =
      Renaming.registry p (replayAt states time word) := by
  unfold replayAt
  rw [related]
  exact replay_transport p injective paired word (states time)

@[simp] theorem saved_renamed [DecidableEq Name] (p : Renaming.Permutation Name) (state : R)
    (name : Name) :
    saved (Renaming.registry p state) (p.toFun name) = (saved state name).map (Renaming.inverse p) := by
  rw [saved, Renaming.registry_at]
  cases found : state name with
  | none => simp [saved, found]
  | some fiber =>
    simp only [saved, found, Option.map_some, Option.getD_some]
    unfold Renaming.fiber
    cases fiber.phase <;> rfl

theorem advance_renamed [DecidableEq Name] (p : Renaming.Permutation Name)
    (before after : R) (actor name : Name) (index : Nat) (stacks pairedStacks : Name → List C)
    (paired : ∀ n, pairedStacks (p.toFun n) = (stacks n).map (Capture.transport p id)) :
    advance (Renaming.registry p before) (Renaming.registry p after) (p.toFun actor) index
      pairedStacks (p.toFun name) =
      (advance before after actor index stacks name).map (Capture.transport p id) := by
  simp only [advance, p.eq_iff, paired, saved_renamed, List.length_map]
  split
  · cases saved after name with
    | nil => rfl
    | cons token rest =>
      simp only [List.map_cons, List.length_cons, List.length_map]
      split <;> rfl
  · rfl

/-- The word used by corrected replay is the actual tracked word of the
renamed history. This holds through pushes, resets, and intervening reuse. -/
theorem track_renamed [DecidableEq Name] (p : Renaming.Permutation Name)
    (states : Nat → R) (actors : Nat → Name) (time : Nat) (name : Name) :
    track (fun index => Renaming.registry p (states index)) (fun index => p.toFun (actors index))
      time (p.toFun name) =
      (track states actors time name).map (Capture.transport p id) := by
  induction time generalizing name with
  | zero => rfl
  | succ time ih => exact advance_renamed p _ _ _ _ _ _ _ ih

theorem replay_tracked_renamed [DecidableEq Name] [DecidableEq Key]
    (p : Renaming.Permutation Name) (states : Nat → R) (actors : Nat → Name) (time : Nat) (actor : Name) :
    replayAt (fun index => Renaming.registry p (states index)) time
      (track (fun index => Renaming.registry p (states index)) (fun index => p.toFun (actors index))
        time (p.toFun actor)) =
      Renaming.registry p (replayAt states time (track states actors time actor)) := by
  rw [track_renamed]
  apply replayAt_transport p (birth := id) (fun _ _ eq => eq) states _ _ _ rfl
  intro name
  simp [birthAt_renamed]

end Cordis.Repairs.IncarnationReplay

namespace Cordis.Renaming
open Calculus Stages
universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "Program" => Code → Instruction Name Key Value Code Error

/-- Structural renaming preserves the label and actor for any choice of
target program that preserves the actual primitive landings. -/
theorem labeled_step_transport (p : Permutation Name) {prog other : Program}
    (landingMap : ∀ {actor code before after token next}, Land prog actor code before after token next →
      Land other (p.toFun actor) code (registry p before) (registry p after) (inverse p token) next)
    {rule : Labeled.Rule} {actor : Name} {before after : R}
    (step : Labeled.Step prog rule actor before after) :
    Labeled.Step other rule (p.toFun actor) (registry p before) (registry p after) := by
  cases step with
  | insert r name component parent ready =>
    simpa only [put_eq, fresh_fiber] using
      Labeled.Step.insert (program := other) (registry p before) (p.toFun actor)
        component (parent.map p.toFun) (insertable_map p before actor component parent ready)
  | retire r name present =>
    simpa only [retire_eq] using
      Labeled.Step.retire (program := other) (registry p before) (p.toFun actor)
        (by simpa using present)
  | remove r name ready =>
    simpa only [erase_eq] using
      Labeled.Step.remove (program := other) (registry p before) (p.toFun actor)
        (removable_map p before actor ready)
  | begin r name f v present inactive errorFree target =>
    simpa only [mark_eq, phase, List.map_nil] using
      Labeled.Step.begin (program := other) (registry p before) (p.toFun actor)
        (fiber p f) (view p v) (by simp [present]) (by simp [fiber, inactive, phase])
        ((errorFree_iff p before actor).mpr errorFree) ((target_iff p before actor v).mpr target)
  | iter r s name f c a v i next present reloading target landing =>
    simpa only [mark_eq, phase, List.map_cons] using
      Labeled.Step.iter (program := other) (registry p before) (registry p s)
        (p.toFun actor) (fiber p f) c (a.map (inverse p)) (view p v) (inverse p i) next
        (by simp [present]) (by simp [fiber, reloading, phase])
        ((target_iff p before actor v).mpr target) (landingMap landing)
  | finish r s name f c a v i present reloading target landing =>
    simpa only [mark_eq, phase, List.map_cons] using
      Labeled.Step.finish (program := other) (registry p before) (registry p s)
        (p.toFun actor) (fiber p f) c (a.map (inverse p)) (view p v) (inverse p i)
        (by simp [present]) (by simp [fiber, reloading, phase])
        ((target_iff p before actor v).mpr target) (landingMap landing)
  | divert r s name f c a v tail present reloading target alternative =>
    have mapped : (registry p s = registry p before ∧ tail.map (inverse p) = []) ∨
        ∃ i next, Land other (p.toFun actor) c (registry p before) (registry p s) i next ∧
          tail.map (inverse p) = [i] := by
      rcases alternative with ⟨same, nil⟩ | ⟨i, next, landing, single⟩
      · exact .inl ⟨congrArg (registry p) same, by simp [nil]⟩
      · exact .inr ⟨inverse p i, next, landingMap landing, by simp [single]⟩
    simpa only [mark_eq, phase, List.map_append] using
      Labeled.Step.divert (program := other) (registry p before) (registry p s)
        (p.toFun actor) (fiber p f) c (a.map (inverse p)) (view p v) (tail.map (inverse p))
        (by simp [present]) (by simp [fiber, reloading, phase])
        (fun ht => target ((target_iff p before actor v).mp ht)) mapped
  | leave r name f a v present active target =>
    simpa only [mark_eq, phase] using
      Labeled.Step.leave (program := other) (registry p before) (p.toFun actor)
        (fiber p f) (a.map (inverse p)) (view p v) (by simp [present]) (by simp [fiber, active, phase])
        (fun ht => target ((target_iff p before actor v).mp ht))
  | unload r name f a v present unloading free =>
    simpa only [mark_eq, discharge_eq, phase] using
      Labeled.Step.unload (program := other) (registry p before) (p.toFun actor)
        (fiber p f) (a.map (inverse p)) (view p v)
        (by simp [present]) (by simp [fiber, unloading, phase])
        (fun hr => free ((relied_iff p before actor).mp hr))

/-- Preserve the rule and actor indices used by the incarnation tracker. -/
theorem labeled_step_map (p : Permutation Name) {prog : Program}
    {rule : Labeled.Rule} {actor : Name} {before after : R}
    (step : Labeled.Step prog rule actor before after) :
    Labeled.Step (program p prog) rule (p.toFun actor) (registry p before) (registry p after) :=
  labeled_step_transport p (land_map p prog) step

theorem labeled_step_equivariant (p : Permutation Name) {prog : Program}
    {rule : Labeled.Rule} {actor : Name} {before after : R} :
    Labeled.Step prog rule actor before after ↔
      Labeled.Step (program p prog) rule (p.toFun actor) (registry p before) (registry p after) := by
  constructor
  · exact labeled_step_map p
  · intro step
    have actorBack : p.symm.toFun (p.toFun actor) = actor := p.left_inv actor
    simpa only [program_symm, registry_symm, actorBack] using labeled_step_map p.symm step

/-- The same program can be used when each instantiation instruction
selects the same next code on a child and its image. -/
def PreservesChildBranches (p : Permutation Name) (prog : Program) : Prop :=
  ∀ code component, (prog code).action = .instantiate component → ∀ child,
    (prog code).next (.child (p.toFun child)) = (prog code).next (.child child)

omit [DecidableEq Name] [DecidableEq Key] in
theorem PreservesChildBranches.symm {p : Permutation Name} {prog : Program}
    (stable : PreservesChildBranches p prog) : PreservesChildBranches p.symm prog := by
  intro code component action child
  simpa [Permutation.symm] using (stable code component action (p.invFun child)).symm

private theorem performed_with_same_action {prog other : Program}
    {actor : Name} {code : Code} {before after : R} {token reply}
    (action : (other code).action = (prog code).action)
    (performed : Performed other actor code before after token reply) : Performed prog actor code before after token reply := by
  cases performed <;> constructor <;> first | assumption | rw [← action]; assumption

/-- A particular successful landing only needs agreement at the child
name that this landing actually draws. -/
theorem land_map_same (p : Permutation Name) {prog : Program}
    {actor : Name} {code : Code} {before after : R} {token next}
    (landed : Land prog actor code before after token next)
    (stable : ∀ name, token = .retire name → (prog code).next (.child (p.toFun name)) = next) :
    Land prog (p.toFun actor) code (registry p before) (registry p after) (inverse p token) next := by
  obtain ⟨reply, performed, result⟩ := land_has_outcome prog landed
  have renamed := performed_map p prog performed
  have native := performed_with_same_action (prog := prog) (other := program p prog) rfl renamed
  have selected : (prog code).next (outcome p reply) = next := by
    cases performed with
    | unit | provide | operate => exact result
    | instantiate _ _ _ component child action _ => exact stable child rfl
  rw [← selected]
  exact native.toLand prog

theorem labeled_step_map_same (p : Permutation Name) {prog : Program} (stable : PreservesChildBranches p prog)
    {rule : Labeled.Rule} {actor : Name} {before after : R}
    (step : Labeled.Step prog rule actor before after) :
    Labeled.Step prog rule (p.toFun actor) (registry p before) (registry p after) := by
  apply labeled_step_transport p _ step
  intro name code source target token next actual
  apply land_map_same p actual
  intro child selected
  cases selected
  cases actual with
  | instantiate _ _ _ component _ action _ => exact stable code component action child

theorem labeled_step_equivariant_same (p : Permutation Name) {prog : Program}
    (stable : PreservesChildBranches p prog) {rule : Labeled.Rule} {actor : Name} {before after : R} :
    Labeled.Step prog rule actor before after ↔ Labeled.Step prog rule (p.toFun actor) (registry p before) (registry p after) := by
  constructor
  · exact labeled_step_map_same p stable
  · intro step
    have actorBack : p.symm.toFun (p.toFun actor) = actor := p.left_inv actor
    simpa only [registry_symm, actorBack] using labeled_step_map_same p.symm stable.symm step

def trace (p : Permutation Name) {prog : Program} {initial : R} {last : Nat}
    (source : Indexed.Trace prog initial last) : Indexed.Trace (program p prog) (registry p initial) last where
  state time := registry p (source.state time)
  rule := source.rule
  actor time := p.toFun (source.actor time)
  start := congrArg (registry p) source.start
  step time bounded := labeled_step_map p (source.step time bounded)

end Cordis.Renaming
