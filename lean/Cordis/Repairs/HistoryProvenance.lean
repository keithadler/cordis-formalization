import Cordis.Repairs.LegalHistory

/-!
Root commands in Definition 74 and Theorem 80 are classified at their point of
execution. Insertion is external and creates a root. Retirement and removal
use the current target's parent. The lifecycle rules preserve the set of
roots, including when an activation creates a child. The root subsequence
therefore needs no classification of names that would outlive their entries.
-/
namespace Cordis.Repairs.LegalHistory
open Calculus Stages OrchestrationSorting CausalCommands
universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
local notation "Cmd" => Command Name Key Code
local notation "Ev" => Event Name Key Code

def rootAt (state : R) (name : Name) : Bool :=
  (state name).any fun fiber => fiber.parent.isNone

def commandRoots (state : R) (command : Cmd) : List Cmd :=
  match command with
  | .insert _ _ => [command]
  | .retire name | .remove name => if rootAt state name then [command] else []

def eventRoots (state : R) (event : Ev) : List Cmd :=
  match event with
  | .command command => commandRoots state command
  | .lifecycle _ _ => []

omit [DecidableEq Name] [DecidableEq Key] in
theorem commandRoots_same_row (command : Cmd) {before after : R}
    (same : before command.actor = after command.actor) :
    commandRoots before command = commandRoots after command := by
  cases command <;> simp_all [commandRoots, rootAt, Command.actor]

omit [DecidableEq Key] in
theorem rootAt_modify (state : R) (actor : Name) (edit : F → F)
    (keepsParent : ∀ row, (edit row).parent = row.parent) (name : Name) :
    rootAt (Calculus.modify state actor edit) name = rootAt state name := by
  by_cases same : name = actor
  · subst name
    cases found : state actor <;> simp [rootAt, Calculus.modify, found, keepsParent]
  · simp [rootAt, Calculus.modify, same]

omit [DecidableEq Key] in
theorem rootAt_child (state : R) (name parent : Name) (component : Component Key Code)
    (absent : state name = none) (query : Name) :
    rootAt (put state name (fresh component (some parent))) query = rootAt state query := by
  by_cases same : query = name
  · subst query
    simp [rootAt, put, fresh, absent]
  · simp [rootAt, put, same]

omit [DecidableEq Key] in
@[simp] theorem rootAt_mark (state : R) (actor : Name) (phase : Phase Name Key Code (Inverse Name Key Value))
    (name : Name) : rootAt (mark state actor phase) name = rootAt state name :=
  rootAt_modify state actor (fun row => {row with phase := phase}) (fun _ => rfl) name

omit [DecidableEq Key] in
@[simp] theorem rootAt_retire (state : R) (actor name : Name) :
    rootAt (Calculus.retire state actor) name = rootAt state name :=
  rootAt_modify state actor (fun row => {row with retired := true}) (fun _ => rfl) name

@[simp] theorem rootAt_write (state : R) (owner : Name) (key : Key) (value : Option Value) (name : Name) :
    rootAt (write state owner key value) name = rootAt state name := by
  unfold write
  apply rootAt_modify
  intro row
  rfl

theorem rootAt_land (program : Code → Instruction Name Key Value Code Error)
    {actor : Name} {code : Code} {before after : R} {inverse next}
    (land : Land program actor code before after inverse next) (name : Name) :
    rootAt after name = rootAt before name := by
  cases land with
  | unit => rfl
  | provide => apply rootAt_write
  | operate => apply rootAt_write
  | instantiate _ _ _ component child _ ready => exact rootAt_child _ child _ component ready.1 name

theorem rootAt_undo (state : R) (inverse : Inverse Name Key Value) (name : Name) :
    rootAt (Stages.undo inverse state) name = rootAt state name := by
  cases inverse with
  | unit => rfl
  | restrict => apply rootAt_write
  | operate =>
    unfold Stages.undo
    apply rootAt_modify
    intro row
    rfl
  | retire => apply rootAt_retire

theorem rootAt_discharge (state : R) (inverses : List (Inverse Name Key Value)) (name : Name) :
    rootAt (discharge Stages.undo inverses state) name = rootAt state name := by
  induction inverses generalizing state with
  | nil => rfl
  | cons inverse rest ih => exact (ih (Stages.undo inverse state)).trans (rootAt_undo state inverse name)

variable {program : Code → Instruction Name Key Value Code Error}

theorem rootAt_lifecycle (kind : Lifecycle) {actor : Name} {before after : R}
    (step : Labeled.Step program kind.rule actor before after) (name : Name) :
    rootAt after name = rootAt before name := by
  cases kind with
  | begin =>
    cases step with
    | begin => apply rootAt_mark
  | iter =>
    cases step with
    | iter _ _ _ _ _ _ _ _ _ _ _ _ land =>
      exact (rootAt_mark _ _ _ _).trans (rootAt_land program land name)
  | finish =>
    cases step with
    | finish _ _ _ _ _ _ _ _ _ _ _ land =>
      exact (rootAt_mark _ _ _ _).trans (rootAt_land program land name)
  | divert =>
    cases step with
    | divert _ _ _ _ _ _ _ _ _ _ _ alternative =>
      rcases alternative with ⟨rfl, _⟩ | ⟨_, _, land, _⟩
      · apply rootAt_mark
      · exact (rootAt_mark _ _ _ _).trans (rootAt_land program land name)
  | leave =>
    cases step with
    | leave => apply rootAt_mark
  | unload =>
    cases step with
    | unload _ _ _ inverses _ _ _ _ =>
      exact (rootAt_mark _ _ _ _).trans (rootAt_discharge _ inverses name)

/-- A new root is created only by the external insertion of that name. -/
theorem root_origin {event : Ev} {before after : R} (step : event.Step program before after)
    (name : Name) (beforeRoot : rootAt before name = false) (afterRoot : rootAt after name = true) :
    ∃ component, event = .command (.insert name component) := by
  cases event with
  | lifecycle kind actor =>
    rw [rootAt_lifecycle kind step name, beforeRoot] at afterRoot
    cases afterRoot
  | command command =>
    obtain ⟨_, rfl⟩ := step
    cases command with
    | insert actor component =>
      by_cases same : name = actor
      · subst actor
        exact ⟨component, rfl⟩
      · simp [Command.apply, rootAt, put, same, show (before name).any (fun row => row.parent.isNone) = false from beforeRoot] at afterRoot
    | retire =>
      change rootAt (Calculus.retire before _) name = true at afterRoot
      rw [rootAt_retire, beforeRoot] at afterRoot
      cases afterRoot
    | remove actor =>
      by_cases same : name = actor
      · subst actor
        simp [Command.apply, rootAt, erase] at afterRoot
      · simp [Command.apply, rootAt, erase, same, show (before name).any (fun row => row.parent.isNone) = false from beforeRoot] at afterRoot

omit [DecidableEq Name] [DecidableEq Key] in
theorem eventRoots_agree (event : Ev) {left right : R}
    (same : ∀ name, rootAt left name = rootAt right name) :
    eventRoots left event = eventRoots right event := by
  cases event with
  | lifecycle => rfl
  | command command => cases command <;> simp [eventRoots, commandRoots, same]

omit [DecidableEq Key] in
theorem rootAt_command_agrees (command : Cmd) {left right : R}
    (same : ∀ name, rootAt left name = rootAt right name) (name : Name) :
    rootAt (command.apply left) name = rootAt (command.apply right) name := by
  cases command with
  | insert actor component =>
    by_cases target : name = actor
    · simp [Command.apply, rootAt, put, target]
    · simpa only [Command.apply, rootAt, put, if_neg target] using same name
  | retire actor =>
    simpa only [Command.apply, rootAt_retire] using same name
  | remove actor =>
    by_cases target : name = actor
    · simp [Command.apply, rootAt, erase, target]
    · simpa only [Command.apply, rootAt, erase, if_neg target] using same name

theorem step_roots_agree {event : Ev} {left right nextLeft nextRight : R}
    (first : event.Step program left nextLeft) (second : event.Step program right nextRight)
    (same : ∀ name, rootAt left name = rootAt right name) (name : Name) :
    rootAt nextLeft name = rootAt nextRight name := by
  cases event with
  | lifecycle kind actor =>
    exact (rootAt_lifecycle kind first name).trans
      ((same name).trans (rootAt_lifecycle kind second name).symm)
  | command command =>
    obtain ⟨_, rfl⟩ := first
    obtain ⟨_, rfl⟩ := second
    exact rootAt_command_agrees command same name

/-- An execution with the root subsequence read from the source of each step.
The index preserves the original command payload, including components. -/
inductive RootExec (program : Code → Instruction Name Key Value Code Error) :
    List Ev → R → R → List Cmd → Prop
  | nil (state) : RootExec program [] state state []
  | cons {event events before middle after roots} : event.Step program before middle →
      RootExec program events middle after roots →
      RootExec program (event :: events) before after (eventRoots before event ++ roots)

theorem RootExec.toExec {events : List Ev} {before after : R} {roots : List Cmd}
    (execution : RootExec program events before after roots) : Exec program events before after := by
  induction execution with
  | nil => exact .nil _
  | cons step _ ih => exact .cons step ih

theorem Exec.withRoots {events : List Ev} {before after : R}
    (execution : Exec program events before after) :
    ∃ roots, RootExec program events before after roots := by
  induction execution with
  | nil => exact ⟨[], .nil _⟩
  | cons step _ ih =>
    obtain ⟨roots, tail⟩ := ih
    exact ⟨_, .cons step tail⟩

theorem RootExec.append {front suffix : List Ev} {before middle after : R} {first second : List Cmd}
    (prefixRun : RootExec program front before middle first)
    (suffixRun : RootExec program suffix middle after second) :
    RootExec program (front ++ suffix) before after (first ++ second) := by
  induction prefixRun with
  | nil => exact suffixRun
  | cons step _ ih =>
    simpa only [List.cons_append, List.append_assoc] using RootExec.cons step (ih suffixRun)

theorem RootExec.split {front suffix : List Ev} {before after : R} {roots : List Cmd}
    (execution : RootExec program (front ++ suffix) before after roots) :
    ∃ middle first second, RootExec program front before middle first ∧
      RootExec program suffix middle after second ∧ roots = first ++ second := by
  induction front generalizing before roots with
  | nil => exact ⟨before, [], roots, .nil before, execution, rfl⟩
  | cons event rest ih =>
    cases execution with
    | cons step tail =>
      obtain ⟨middle, first, second, firstRun, secondRun, equal⟩ := ih tail
      exact ⟨middle, _, second, .cons step firstRun, secondRun, by rw [equal, List.append_assoc]⟩

/-- Different child draws in the same event sequence cannot change its root
subsequence. Each event updates root membership deterministically. -/
theorem RootExec.roots_agree {events : List Ev} {left right leftFinal rightFinal : R}
    {leftRoots rightRoots : List Cmd}
    (first : RootExec program events left leftFinal leftRoots)
    (second : RootExec program events right rightFinal rightRoots)
    (same : ∀ name, rootAt left name = rootAt right name) :
    leftRoots = rightRoots := by
  induction first generalizing right rightFinal rightRoots with
  | nil => cases second; rfl
  | cons step _ ih =>
    cases second with
    | cons other tail =>
      rw [eventRoots_agree _ same, ih tail (step_roots_agree step other same)]

/-- Exchanging neighboring enabled commands with distinct targets preserves
the actual root subsequence if at least one command is on a child. -/
theorem RootExec.exchange_commands (first second : Cmd)
    {front suffix : List Ev} {initial before middle after final : R}
    {prefixRoots suffixRoots : List Cmd}
    (prefixRun : RootExec program front initial before prefixRoots)
    (a : first.Step before middle) (b : second.Step middle after)
    (suffixRun : RootExec program suffix after final suffixRoots)
    (different : first.actor ≠ second.actor) (earlier : second.Enabled before)
    (oneChild : commandRoots before first = [] ∨ commandRoots middle second = []) :
    RootExec program (front ++ .command second :: .command first :: suffix) initial final
      (prefixRoots ++ (commandRoots before first ++ (commandRoots middle second ++ suffixRoots))) := by
  obtain ⟨swapped, firstStep, secondStep⟩ := command_diamond first second a b different earlier
  have firstSame : commandRoots swapped first = commandRoots before first := by
    apply commandRoots_same_row
    rw [firstStep.2]
    exact apply_other second before first.actor different
  have secondSame : commandRoots middle second = commandRoots before second := by
    apply commandRoots_same_row
    rw [a.2]
    exact apply_other first before second.actor (Ne.symm different)
  have result := prefixRun.append (RootExec.cons (event := .command second) firstStep
    (RootExec.cons (event := .command first) secondStep suffixRun))
  change RootExec program _ _ _
    (prefixRoots ++ (commandRoots before second ++ (commandRoots swapped first ++ suffixRoots))) at result
  rw [firstSame, ← secondSame] at result
  rcases oneChild with h | h <;> simpa [h] using result

/-- Activation has no root birth. Swapping with an admissible orchestration
command preserves the command's classification even when names can be reused. -/
theorem RootExec.exchange_activation (kind : Lifecycle) (actor : Name) (command : Cmd)
    {front suffix : List Ev} {initial before middle after final : R}
    {prefixRoots suffixRoots : List Cmd}
    (prefixRun : RootExec program front initial before prefixRoots)
    (activation : Labeled.Step program kind.rule actor before middle)
    (active : Transposition.Activation kind.rule) (external : command.Step middle after)
    (suffixRun : RootExec program suffix after final suffixRoots)
    (different : actor ≠ command.actor)
    (notCreated : before command.actor = none → middle command.actor = none) :
    RootExec program (front ++ .command command :: .lifecycle kind actor :: suffix) initial final
      (prefixRoots ++ (commandRoots middle command ++ suffixRoots)) := by
  obtain ⟨enabled, rfl⟩ := external
  obtain ⟨earlier, swapped⟩ := activation_command_diamond program command activation active enabled different notCreated
  have same : commandRoots before command = commandRoots middle command := by
    cases command with
    | insert => rfl
    | retire name => simp only [commandRoots, rootAt_lifecycle kind activation name]
    | remove name => simp only [commandRoots, rootAt_lifecycle kind activation name]
  have result := prefixRun.append (RootExec.cons (event := .command command) ⟨earlier, rfl⟩
    (RootExec.cons (event := .lifecycle kind actor) swapped suffixRun))
  change RootExec program _ _ _ (prefixRoots ++ (commandRoots before command ++ suffixRoots)) at result
  rwa [same] at result

omit [DecidableEq Name] [DecidableEq Key] in
/-- The root can cross the child command only if the names differ and
the child removal does not release a reservation or establish a leaf guard
needed by the root command. -/
def rootMayCrossChild (first second : Cmd) (before : R) : Prop :=
  first.actor ≠ second.actor ∧
  match first, second with
  | .remove removed, .insert _ component =>
    ∀ row, before removed = some row → ∀ key, component.provides key → ¬ row.component.provides key
  | .remove removed, .remove parent =>
    ∀ row, before removed = some row → row.parent ≠ some parent
  | _, _ => True

private theorem child_retire_root_distinct (name : Name) (second : Cmd) {before after : R}
    (present : before name ≠ none) (childClass : commandRoots before (.retire name) = [])
    (root : second.Step (Calculus.retire before name) after)
    (rootClass : commandRoots (Calculus.retire before name) second ≠ []) : name ≠ second.actor := by
  intro same
  have oldChild : rootAt before name = false := by
    cases flagged : rootAt before name <;> simp [commandRoots, flagged] at childClass ⊢
  cases second with
  | insert actor component =>
    change name = actor at same
    subst actor
    exact present ((Transposition.retire_presence _ _ _).mp root.1.1)
  | retire actor | remove actor =>
    change name = actor at same
    subst actor
    exact rootClass (by simp [commandRoots, oldChild])

/-- An adjacent child command and root command can exchange exactly when
the earlier cut admits the root command. -/
theorem child_root_command_exchange (first second : Cmd) {before middle after : R}
    (child : first.Step before middle) (root : second.Step middle after)
    (childClass : commandRoots before first = []) (rootClass : commandRoots middle second ≠ []) :
    (∃ swapped, second.Step before swapped ∧ first.Step swapped after) ↔
      rootMayCrossChild first second before := by
  have ready : second.Enabled before ↔ rootMayCrossChild first second before := by
    unfold rootMayCrossChild
    obtain ⟨firstReady, rfl⟩ := child
    cases first with
    | insert => simp [commandRoots] at childClass
    | retire name =>
      have different := child_retire_root_distinct name second firstReady childClass root rootClass
      have oldReady := (enabled_retire_other before second (Ne.symm different)).mp root.1
      cases second <;> exact ⟨fun _ => ⟨different, trivial⟩, fun _ => oldReady⟩
    | remove removed =>
      by_cases same : second.actor = removed
      · cases second with
        | insert name component =>
          change name = removed at same
          subst name
          have no : ¬ (Command.insert removed component).Enabled before :=
            fun inactive => Transposition.removable_present before removed firstReady inactive.1
          simp [Command.actor, no]
        | retire name =>
          change name = removed at same
          subst name
          have live : erase before removed removed ≠ none := root.1
          exact False.elim (live (by simp [erase]))
        | remove name =>
          change name = removed at same
          subst name
          have present := Transposition.removable_present (erase before removed) removed root.1
          exact False.elim (present (by simp [erase]))
      · have different : removed ≠ second.actor := Ne.symm same
        cases second with
        | insert name component =>
          change name ≠ removed at same
          change removed ≠ name at different
          change Insertable before name component none ↔ removed ≠ name ∧ _
          rw [root_insertable_before_erase before same component]
          exact ⟨fun enabled => ⟨different, enabled.2⟩, fun allowed => ⟨root.1, allowed.2⟩⟩
        | retire name =>
          change name ≠ removed at same
          change removed ≠ name at different
          have live : erase before removed name ≠ none := root.1
          rw [Transposition.erase_other _ _ _ same] at live
          simp [Command.Enabled, Command.actor, different, live]
        | remove parent =>
          change parent ≠ removed at same
          change removed ≠ parent at different
          change Removable before parent ↔ removed ≠ parent ∧ _
          rw [removable_before_erase before same]
          exact ⟨fun enabled => ⟨different, enabled.2⟩, fun allowed => ⟨root.1, allowed.2⟩⟩
  constructor
  · rintro ⟨_, earliest, _⟩
    exact ready.mp earliest.1
  · intro enabled
    exact command_diamond first second child root enabled.1 (ready.mpr enabled)

/-- A child removal can free a name, release a provision declaration, or
make its parent a leaf. Each can be required by the following root command. -/
inductive ChildRemovalBarrier (before : R) : Cmd → Cmd → Prop
  | nameReuse (name : Name) (component : Component Key Code) :
      ChildRemovalBarrier before (.remove name) (.insert name component)
  | provision {removed actor : Name} {component : Component Key Code} {row : F} {key : Key} :
      before removed = some row → row.component.provides key → component.provides key →
      ChildRemovalBarrier before (.remove removed) (.insert actor component)
  | leaf {removed parent : Name} {row : F} :
      before removed = some row → row.parent = some parent →
      ChildRemovalBarrier before (.remove removed) (.remove parent)

omit [DecidableEq Name] [DecidableEq Key] in
theorem ChildRemovalBarrier.blocks {before : R} {first second : Cmd}
    (barrier : ChildRemovalBarrier before first second) : ¬ rootMayCrossChild first second before := by
  intro allowed
  cases barrier with
  | nameReuse => exact allowed.1 rfl
  | provision found reserved requested => exact allowed.2 _ found _ requested reserved
  | leaf found parent => exact allowed.2 _ found parent

/-- The obstructions for a legal child-root pair are exactly the three
ways a child removal can enable the next root command. -/
theorem child_root_barrier_iff (first second : Cmd) {before middle after : R}
    (child : first.Step before middle) (root : second.Step middle after)
    (childClass : commandRoots before first = []) (rootClass : commandRoots middle second ≠ []) :
    (¬ rootMayCrossChild first second before) ↔ ChildRemovalBarrier before first second := by
  refine ⟨?_, ChildRemovalBarrier.blocks⟩
  intro blocked
  obtain ⟨ready, rfl⟩ := child
  cases first with
  | insert => simp [commandRoots] at childClass
  | retire name =>
    have different := child_retire_root_distinct name second ready childClass root rootClass
    exact False.elim (blocked ⟨different, trivial⟩)
  | remove removed =>
    cases second with
    | insert actor component =>
      by_cases equal : removed = actor
      · subst actor
        exact .nameReuse removed component
      · apply Classical.byContradiction
        intro none
        apply blocked
        refine ⟨equal, ?_⟩
        intro row found key requested reserved
        exact none (.provision found reserved requested)
    | retire actor =>
      have different : removed ≠ actor := by
        intro equal
        subst actor
        have live : erase before removed removed ≠ none := root.1
        exact live (by simp [erase])
      exact False.elim (blocked ⟨different, trivial⟩)
    | remove parent =>
      have different : removed ≠ parent := by
        intro equal
        subst parent
        exact Transposition.removable_present (erase before removed) removed root.1 (by simp [erase])
      apply Classical.byContradiction
      intro none
      apply blocked
      refine ⟨different, ?_⟩
      intro row found parent
      exact none (.leaf found parent)

end Cordis.Repairs.LegalHistory
