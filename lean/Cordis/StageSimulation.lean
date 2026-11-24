import Cordis.GuardObservations
import Cordis.Labeled

/-! A constructive, control-aware simulation fragment for Lemma60.

`Related Q` retains every registry control field, relates code through an
explicit relation Q, and relates captured inverse constructors and functions.
`ProgramsRelated` is a local contract on primitive callbacks and outcome-chosen
continuations, not a premise asserting state-transition preservation.

This is a sufficient structural relation. It is not identified silently with
Equation54's semantic function lifting: the paper must specify which state
relation that lifting uses before that equivalence can be claimed. In
particular, provision/instantiation and their actual captured inverses are
handled here with their control effects retained, not erased to table equality.
-/
namespace Cordis.StageSimulation
open Calculus Stages Iterators
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
variable [DecidableEq Name] [DecidableEq Key] [Setoid Value]
set_option linter.unusedSectionVars false

inductive InverseRelated : Inverse Name Key Value → Inverse Name Key Value → Prop
  | unit : InverseRelated .unit .unit
  | restrict (owner key) : InverseRelated (.restrict owner key) (.restrict owner key)
  | operate (owner key) {f g : Value → Value} : Effects.Related f g →
      InverseRelated (.operate owner key f) (.operate owner key g)
  | retire (child) : InverseRelated (.retire child) (.retire child)

inductive StackRelated : List (Inverse Name Key Value) → List (Inverse Name Key Value) → Prop
  | nil : StackRelated [] []
  | cons {a b as bs} : InverseRelated a b → StackRelated as bs → StackRelated (a :: as) (b :: bs)

inductive PhaseRelated (Q : Code → Code → Prop) :
    Phase Name Key Code (Inverse Name Key Value) → Phase Name Key Code (Inverse Name Key Value) → Prop
  | inactive : PhaseRelated Q .inactive .inactive
  | reloading {a b as bs} (view) : Q a b → StackRelated as bs →
      PhaseRelated Q (.reloading a as view) (.reloading b bs view)
  | active {as bs} (view) : StackRelated as bs → PhaseRelated Q (.active as view) (.active bs view)
  | unloading {as bs} (view) : StackRelated as bs → PhaseRelated Q (.unloading as view) (.unloading bs view)

structure ComponentRelated (Q : Code → Code → Prop) (a b : Component Key Code) : Prop where
  requires : a.requires = b.requires
  provides : a.provides = b.provides
  entry : Q a.entry b.entry

structure FiberRelated (Q : Code → Code → Prop) (a b : F) : Prop where
  component : ComponentRelated Q a.component b.component
  parent : a.parent = b.parent
  retired : a.retired = b.retired
  phase : PhaseRelated Q a.phase b.phase
  table : ∀ key, OptionRel (fun v w : Value => v ≈ w) (a.table key) (b.table key)

def Related (Q : Code → Code → Prop) (r s : R) : Prop :=
  ∀ name, OptionRel (FiberRelated Q) (r name) (s name)

theorem PhaseRelated.observed {Q : Code → Code → Prop} {a b : Phase Name Key Code (Inverse Name Key Value)}
    (related : PhaseRelated Q a b) :
    GuardObservations.phaseKind a = GuardObservations.phaseKind b ∧ a.committed = b.committed := by
  cases related <;> exact ⟨rfl, rfl⟩

theorem FiberRelated.observed {Q : Code → Code → Prop} {a b : F} (related : FiberRelated Q a b) :
    GuardObservations.FiberRelated a b :=
  ⟨⟨related.component.requires, related.component.provides, related.parent, related.retired,
    related.phase.observed.1, related.phase.observed.2⟩, related.table⟩

theorem Related.observed {Q : Code → Code → Prop} {r s : R} (related : Related Q r s) :
    GuardObservations.Related r s := by
  intro n
  exact OptionRel.mono (fun _ _ h => h.observed) (related n)

theorem Related.tables {Q : Code → Code → Prop} {r s : R} (related : Related Q r s) :
    StageRecovery.TablesRelated r s := by
  intro owner key
  have pair := related owner
  cases left : r owner <;> cases right : s owner <;>
    simp only [left, right, OptionRel, StageRecovery.tableAt, Option.bind_none, Option.bind_some] at pair ⊢
  exact pair.table key

theorem ComponentRelated.eq_of_codes {left right : Component Key Code} (related : ComponentRelated Eq left right) :
    left = right := by
  rcases left with ⟨requires, provides, entry⟩
  rcases right with ⟨requires', provides', entry'⟩
  obtain ⟨rfl, rfl, rfl⟩ := related
  rfl

theorem present_related {Q : Code → Code → Prop} {r s : R} (related : Related Q r s)
    (n : Name) (a : F) (present : r n = some a) : ∃ b, s n = some b ∧ FiberRelated Q a b := by
  have observed := related n
  rw [present] at observed
  cases found : s n with
  | none => simp [found, OptionRel] at observed
  | some b => exact ⟨b, rfl, by simpa [found, OptionRel] using observed⟩

theorem modify_related {Q : Code → Code → Prop} {r s : R} (related : Related Q r s)
    (name : Name) (f g : F → F)
    (preserves : ∀ a b, FiberRelated Q a b → FiberRelated Q (f a) (g b)) :
    Related Q (Calculus.modify r name f) (Calculus.modify s name g) := by
  intro n
  by_cases same : n = name
  · subst n
    have pair := related name
    cases ha : r name <;> cases hb : s name <;> simp_all [Calculus.modify, OptionRel]
  · simpa [Calculus.modify, same] using related n

theorem put_related {Q : Code → Code → Prop} {r s : R} (related : Related Q r s)
    (name : Name) {a b : F} (pair : FiberRelated Q a b) : Related Q (put r name a) (put s name b) := by
  intro n
  by_cases same : n = name
  · simpa [put, same, OptionRel] using pair
  · simpa [put, same] using related n

theorem erase_related {Q : Code → Code → Prop} {r s : R} (related : Related Q r s)
    (name : Name) : Related Q (erase r name) (erase s name) := by
  intro n
  by_cases same : n = name
  · simp [erase, same, OptionRel]
  · simpa [erase, same] using related n

theorem fresh_related {Q : Code → Code → Prop} {a b : Component Key Code}
    (related : ComponentRelated Q a b) (parent : Option Name) :
    FiberRelated Q (fresh a parent : F) (fresh b parent) :=
  ⟨related, rfl, rfl, .inactive, fun _ => trivial⟩

theorem write_related {Q : Code → Code → Prop} {r s : R} (related : Related Q r s)
    (owner : Name) (key : Key) {a b : Option Value} (values : OptionRel (fun v w : Value => v ≈ w) a b) :
    Related Q (write r owner key a) (write s owner key b) := by
  apply modify_related related owner
  intro f g fg
  refine ⟨fg.component, fg.parent, fg.retired, fg.phase, ?_⟩
  intro k
  by_cases same : k = key
  · simpa [same] using values
  · simpa [same] using fg.table k

theorem retire_related {Q : Code → Code → Prop} {r s : R} (related : Related Q r s)
    (child : Name) : Related Q (Calculus.retire r child) (Calculus.retire s child) := by
  apply modify_related related child
  intro f g fg
  exact ⟨fg.component, fg.parent, rfl, fg.phase, fg.table⟩

theorem mark_related {Q : Code → Code → Prop} {r s : R} (related : Related Q r s)
    (actor : Name) {a b : Phase Name Key Code (Inverse Name Key Value)} (phases : PhaseRelated Q a b) :
    Related Q (mark r actor a) (mark s actor b) := by
  apply modify_related related actor
  intro f g fg
  exact ⟨fg.component, fg.parent, fg.retired, phases, fg.table⟩

theorem undo_related {Q : Code → Code → Prop} {r s : R} (related : Related Q r s)
    {a b : Inverse Name Key Value} (inverses : InverseRelated a b) :
    Related Q (Stages.undo a r) (Stages.undo b s) := by
  cases inverses with
  | unit => exact related
  | restrict owner key => exact write_related related owner key trivial
  | retire child => exact retire_related related child
  | operate owner key fg =>
    apply modify_related related owner
    intro f g pair
    refine ⟨pair.component, pair.parent, pair.retired, pair.phase, ?_⟩
    intro k
    by_cases same : k = key
    · subst k
      have values := pair.table key
      cases hf : f.table key <;> cases hg : g.table key <;> simp_all [OptionRel]
      exact fg values
    · simpa [same] using pair.table k

theorem discharge_related {Q : Code → Code → Prop} {r s : R} (related : Related Q r s)
    {as bs : List (Inverse Name Key Value)} (stacks : StackRelated as bs) :
    Related Q (discharge Stages.undo as r) (discharge Stages.undo bs s) := by
  induction stacks generalizing r s with
  | nil => exact related
  | cons heads tails ih => exact ih (undo_related related heads)

inductive OutcomeRelated : Outcome Name Value → Outcome Name Value → Prop
  | unit : OutcomeRelated .unit .unit
  | value {v w : Value} : v ≈ w → OutcomeRelated (.value v) (.value w)
  | child (name) : OutcomeRelated (.child name) (.child name)

/-- Callback congruence includes both dynamically captured inverses and the
returned outcome; no conclusion about a whole registry is assumed. -/
def CallbackRelated : Except Error (Value × (Value → Value) × Value) →
    Except Error (Value × (Value → Value) × Value) → Prop
  | .error e, .error f => e = f
  | .ok a, .ok b => a.1 ≈ b.1 ∧ Effects.Related a.2.1 b.2.1 ∧ a.2.2 ≈ b.2.2
  | _, _ => False

inductive ActionRelated (Q : Code → Code → Prop) :
    Action Name Key Value Code Error → Action Name Key Value Code Error → Prop
  | unit : ActionRelated Q .unit .unit
  | provide (key) {a b : Value} : a ≈ b → ActionRelated Q (.provide key a) (.provide key b)
  | operate (key) {f g : Value → Except Error (Value × (Value → Value) × Value)} :
      (∀ a b, a ≈ b → CallbackRelated (f a) (g b)) → ActionRelated Q (.operate key f) (.operate key g)
  | instantiate {a b : Component Key Code} : ComponentRelated Q a b →
      ActionRelated Q (.instantiate a) (.instantiate b)

structure ProgramsRelated (Q : Code → Code → Prop)
    (program other : Code → Instruction Name Key Value Code Error) : Prop where
  action : ∀ a b, Q a b → ActionRelated Q (program a).action (other b).action
  next : ∀ a b, Q a b → ∀ x y, OutcomeRelated x y →
    OptionRel Q ((program a).next x) ((other b).next y)

theorem insertable_related {Q : Code → Code → Prop} {r s : R} (related : Related Q r s)
    (name : Name) {a b : Component Key Code} (components : ComponentRelated Q a b) (parent : Option Name)
    (ready : Insertable r name a parent) : Insertable s name b parent := by
  have ready' := (GuardObservations.insertable_iff related.observed name a parent).mp ready
  exact ⟨ready'.1, ready'.2.1, by simpa only [Insertable, ← components.provides] using ready'.2.2⟩

/-- Every successful primitive has a corresponding actual successful primitive
with related state, captured inverse, and returned outcome. Fresh insertion
chooses the same available child name on both sides. -/
theorem performed_simulation {Q : Code → Code → Prop}
    {program other : Code → Instruction Name Key Value Code Error}
    (programs : ProgramsRelated Q program other)
    {actor : Name} {a b : Code} {r r' s : R} {inverse : Inverse Name Key Value}
    {outcome : Outcome Name Value} (codes : Q a b) (related : Related Q r s)
    (performed : Performed program actor a r r' inverse outcome) :
    ∃ s' inverse' outcome', Performed other actor b s s' inverse' outcome' ∧
      Related Q r' s' ∧ InverseRelated inverse inverse' ∧ OutcomeRelated outcome outcome' := by
  have actions := programs.action a b codes
  cases performed with
  | unit r actor a action =>
    rw [action] at actions
    generalize hother : (other b).action = otherAction at actions
    cases actions with
    | unit => exact ⟨s, .unit, .unit, .unit s actor b hother, related, .unit, .unit⟩
  | provide r actor a fiber key value action present allowed absent =>
    rw [action] at actions
    generalize hother : (other b).action = otherAction at actions
    cases actions with
    | provide _ values =>
      obtain ⟨counterpart, found, fibers⟩ := present_related related actor fiber present
      refine ⟨_, _, _, .provide s actor b counterpart key _ hother found ?_ ?_,
        write_related related actor key values, .restrict actor key, .value values⟩
      · simpa only [← fibers.component.provides] using allowed
      · exact (GuardObservations.table_none_iff fibers.observed key).mp absent
  | operate r actor a key run owner before after inverse outcome action located returned =>
    rw [action] at actions
    generalize hother : (other b).action = otherAction at actions
    cases actions with
    | operate _ callbacks =>
      obtain ⟨before', location', values⟩ := GuardObservations.location_success related.observed actor owner key before located
      have outputs := callbacks before before' values
      rw [returned] at outputs
      rename_i run'
      cases returned' : run' before' with
      | error err => simp [returned', CallbackRelated] at outputs
      | ok triple =>
        rcases triple with ⟨after', inverse', outcome'⟩
        have parts : after ≈ after' ∧ Effects.Related inverse inverse' ∧ outcome ≈ outcome' := by
          simpa [returned', CallbackRelated] using outputs
        exact ⟨_, _, _, .operate s actor b key run' owner before' after' inverse' outcome' hother location' returned',
          write_related related owner key parts.1, .operate owner key parts.2.1, .value parts.2.2⟩
  | instantiate r actor a component child action ready =>
    rw [action] at actions
    generalize hother : (other b).action = otherAction at actions
    cases actions with
    | instantiate components =>
      exact ⟨_, _, _, .instantiate s actor b _ child hother (insertable_related related child components (some actor) ready),
        put_related related child (fresh_related components (some actor)), .retire child, .child child⟩

theorem land_performed {program : Code → Instruction Name Key Value Code Error}
    {actor : Name} {code : Code} {r s : R} {inverse : Inverse Name Key Value} {next : Option Code}
    (landed : Land program actor code r s inverse next) :
    ∃ outcome, Performed program actor code r s inverse outcome ∧ (program code).next outcome = next := by
  cases landed with
  | unit r actor code action => exact ⟨_, .unit r actor code action, rfl⟩
  | provide r actor code fiber key value action present allowed absent =>
    exact ⟨_, .provide r actor code fiber key value action present allowed absent, rfl⟩
  | operate r actor code key run owner before after inverse result action located returned =>
    exact ⟨_, .operate r actor code key run owner before after inverse result action located returned, rfl⟩
  | instantiate r actor code component child action ready =>
    exact ⟨_, .instantiate r actor code component child action ready, rfl⟩

theorem land_simulation {Q : Code → Code → Prop}
    {program other : Code → Instruction Name Key Value Code Error}
    (programs : ProgramsRelated Q program other)
    {actor : Name} {a b : Code} {r r' s : R} {inverse : Inverse Name Key Value} {next : Option Code}
    (codes : Q a b) (related : Related Q r s)
    (landed : Land program actor a r r' inverse next) :
    ∃ s' inverse' next', Land other actor b s s' inverse' next' ∧
      Related Q r' s' ∧ InverseRelated inverse inverse' ∧ OptionRel Q next next' := by
  obtain ⟨outcome, performed, selected⟩ := land_performed landed
  obtain ⟨s', inverse', outcome', paired, states, inverses, outcomes⟩ :=
    performed_simulation programs codes related performed
  exact ⟨s', inverse', (other b).next outcome', paired.toLand other, states, inverses,
    by simpa only [selected] using programs.next a b codes outcome outcome' outcomes⟩

theorem phase_inactive {Q : Code → Code → Prop} {phase : Phase Name Key Code (Inverse Name Key Value)}
    (related : PhaseRelated Q .inactive phase) : phase = .inactive := by
  cases phase <;> cases related
  rfl

theorem phase_reloading {Q : Code → Code → Prop} {a : Code} {as : List (Inverse Name Key Value)}
    {view : View Name Key} {phase : Phase Name Key Code (Inverse Name Key Value)}
    (related : PhaseRelated Q (.reloading a as view) phase) :
    ∃ b bs, phase = .reloading b bs view ∧ Q a b ∧ StackRelated as bs := by
  cases phase <;> cases related
  exact ⟨_, _, rfl, by assumption, by assumption⟩

theorem phase_active {Q : Code → Code → Prop} {as : List (Inverse Name Key Value)}
    {view : View Name Key} {phase : Phase Name Key Code (Inverse Name Key Value)}
    (related : PhaseRelated Q (.active as view) phase) :
    ∃ bs, phase = .active bs view ∧ StackRelated as bs := by
  cases phase <;> cases related
  exact ⟨_, rfl, by assumption⟩

theorem phase_unloading {Q : Code → Code → Prop} {as : List (Inverse Name Key Value)}
    {view : View Name Key} {phase : Phase Name Key Code (Inverse Name Key Value)}
    (related : PhaseRelated Q (.unloading as view) phase) :
    ∃ bs, phase = .unloading bs view ∧ StackRelated as bs := by
  cases phase <;> cases related
  exact ⟨_, rfl, by assumption⟩

/-- Lift simulation of successful landings to the labeled rules. -/
theorem step_simulation_of_land {Q : Code → Code → Prop}
    {program other : Code → Instruction Name Key Value Code Error}
    (land : ∀ {actor : Name} {a b : Code} {r r' s : R}
      {inverse : Inverse Name Key Value} {next : Option Code},
      Q a b → Related Q r s → Land program actor a r r' inverse next →
      ∃ s' inverse' next', Land other actor b s s' inverse' next' ∧
        Related Q r' s' ∧ InverseRelated inverse inverse' ∧ OptionRel Q next next')
    (candidates : ∀ code, ∃ counterpart, Q code counterpart)
    {rule : Labeled.Rule} {actor : Name} {r r' s : R} (related : Related Q r s)
    (step : Labeled.Step program rule actor r r') :
    ∃ s', Labeled.Step other rule actor s s' ∧ Related Q r' s' := by
  cases step with
  | insert _ _ component parent ready =>
    obtain ⟨entry, codes⟩ := candidates component.entry
    let counterpart : Component Key Code := { component with entry := entry }
    have components : ComponentRelated Q component counterpart := ⟨rfl, rfl, codes⟩
    exact ⟨_, .insert s actor counterpart parent (insertable_related related actor components parent ready),
      put_related related actor (fresh_related components parent)⟩
  | retire _ _ present =>
    exact ⟨_, .retire s actor (fun absent => present ((GuardObservations.none_iff related.observed actor).mpr absent)),
      retire_related related actor⟩
  | remove _ _ ready =>
    exact ⟨_, .remove s actor ((GuardObservations.removable_iff related.observed actor).mp ready), erase_related related actor⟩
  | begin _ _ fiber view present phase free target =>
    obtain ⟨counterpart, found, fibers⟩ := present_related related actor fiber present
    have phase' := phase_inactive (phase ▸ fibers.phase)
    exact ⟨_, .begin s actor counterpart view found phase'
      ((GuardObservations.errorFree_iff related.observed actor).mp free)
      ((GuardObservations.target_iff related.observed actor view).mp target),
      mark_related related actor (.reloading view fibers.component.entry .nil)⟩
  | iter _ middle _ fiber code stack view inverse next present phase target landed =>
    obtain ⟨counterpart, found, fibers⟩ := present_related related actor fiber present
    obtain ⟨code', stack', phase', codes, stacks⟩ := phase_reloading (phase ▸ fibers.phase)
    obtain ⟨middle', inverse', next', landed', states, inverses, selected⟩ := land codes related landed
    cases next' with
    | none => simp [OptionRel] at selected
    | some rest =>
      exact ⟨_, .iter s middle' actor counterpart code' stack' view inverse' rest found phase'
        ((GuardObservations.target_iff related.observed actor view).mp target) landed',
        mark_related states actor (.reloading view selected (.cons inverses stacks))⟩
  | finish _ middle _ fiber code stack view inverse present phase target landed =>
    obtain ⟨counterpart, found, fibers⟩ := present_related related actor fiber present
    obtain ⟨code', stack', phase', codes, stacks⟩ := phase_reloading (phase ▸ fibers.phase)
    obtain ⟨middle', inverse', next', landed', states, inverses, selected⟩ := land codes related landed
    cases next' with
    | some rest => simp [OptionRel] at selected
    | none =>
      exact ⟨_, .finish s middle' actor counterpart code' stack' view inverse' found phase'
        ((GuardObservations.target_iff related.observed actor view).mp target) landed',
        mark_related states actor (.active view (.cons inverses stacks))⟩
  | divert _ middle _ fiber code stack view tail present phase target alternative =>
    obtain ⟨counterpart, found, fibers⟩ := present_related related actor fiber present
    obtain ⟨code', stack', phase', codes, stacks⟩ := phase_reloading (phase ▸ fibers.phase)
    have target' : ¬ Target s actor view := fun ready => target ((GuardObservations.target_iff related.observed actor view).mpr ready)
    rcases alternative with ⟨rfl, rfl⟩ | ⟨inverse, next, landed, rfl⟩
    · exact ⟨_, .divert s s actor counterpart code' stack' view [] found phase' target' (.inl ⟨rfl, rfl⟩),
        mark_related related actor (.unloading view stacks)⟩
    · obtain ⟨middle', inverse', next', landed', states, inverses, _⟩ := land codes related landed
      exact ⟨_, .divert s middle' actor counterpart code' stack' view [inverse'] found phase' target'
        (.inr ⟨inverse', next', landed', rfl⟩), mark_related states actor (.unloading view (.cons inverses stacks))⟩
  | leave _ _ fiber stack view present phase target =>
    obtain ⟨counterpart, found, fibers⟩ := present_related related actor fiber present
    obtain ⟨stack', phase', stacks⟩ := phase_active (phase ▸ fibers.phase)
    exact ⟨_, .leave s actor counterpart stack' view found phase'
      (fun ready => target ((GuardObservations.target_iff related.observed actor view).mpr ready)),
      mark_related related actor (.unloading view stacks)⟩
  | unload _ _ fiber stack view present phase unrelied =>
    obtain ⟨counterpart, found, fibers⟩ := present_related related actor fiber present
    obtain ⟨stack', phase', stacks⟩ := phase_unloading (phase ▸ fibers.phase)
    exact ⟨_, .unload s actor counterpart stack' view found phase'
      (fun relied => unrelied ((GuardObservations.relied_iff related.observed actor).mpr relied)),
      mark_related (discharge_related related stacks) actor .inactive⟩

/-- All nine actual labeled rules preserve the constructive relation. The
candidate-code premise is used only for a new external O-Insert, whose entry
code is not present in either related source registry. -/
theorem step_simulation {Q : Code → Code → Prop}
    {program other : Code → Instruction Name Key Value Code Error}
    (programs : ProgramsRelated Q program other) (candidates : ∀ code, ∃ counterpart, Q code counterpart)
    {rule : Labeled.Rule} {actor : Name} {r r' s : R} (related : Related Q r s)
    (step : Labeled.Step program rule actor r r') :
    ∃ s', Labeled.Step other rule actor s s' ∧ Related Q r' s' :=
  step_simulation_of_land (land_simulation programs) candidates related step

theorem InverseRelated.symm {a b : Inverse Name Key Value} (related : InverseRelated a b) :
    InverseRelated b a := by
  cases related with
  | unit => exact .unit
  | restrict n k => exact .restrict n k
  | retire n => exact .retire n
  | operate n k functions =>
    exact .operate n k (fun {_ _} related => Setoid.symm (functions (Setoid.symm related)))

theorem StackRelated.symm {as bs : List (Inverse Name Key Value)} (related : StackRelated as bs) :
    StackRelated bs as := by
  induction related with
  | nil => exact .nil
  | cons heads tails ih => exact .cons heads.symm ih

theorem PhaseRelated.symm {Q : Code → Code → Prop} (symmetric : ∀ a b, Q a b → Q b a)
    {a b : Phase Name Key Code (Inverse Name Key Value)} (related : PhaseRelated Q a b) :
    PhaseRelated Q b a := by
  cases related with
  | inactive => exact .inactive
  | reloading view codes stacks => exact .reloading view (symmetric _ _ codes) stacks.symm
  | active view stacks => exact .active view stacks.symm
  | unloading view stacks => exact .unloading view stacks.symm

theorem ComponentRelated.symm {Q : Code → Code → Prop} (symmetric : ∀ a b, Q a b → Q b a)
    {a b : Component Key Code} (related : ComponentRelated Q a b) : ComponentRelated Q b a :=
  ⟨related.requires.symm, related.provides.symm, symmetric _ _ related.entry⟩

theorem FiberRelated.symm {Q : Code → Code → Prop} (symmetric : ∀ a b, Q a b → Q b a)
    {a b : F} (related : FiberRelated Q a b) : FiberRelated Q b a := by
  refine ⟨related.component.symm symmetric, related.parent.symm, related.retired.symm,
    related.phase.symm symmetric, ?_⟩
  intro k
  exact @OptionRel.mono Value Value (fun x y => y ≈ x) (fun x y => x ≈ y)
    (fun _ _ h => Setoid.symm h) _ _ (OptionRel.symm (related.table k))

theorem Related.symm {Q : Code → Code → Prop} (symmetric : ∀ a b, Q a b → Q b a)
    {r s : R} (related : Related Q r s) : Related Q s r := by
  intro n
  exact OptionRel.mono (fun _ _ h => h.symm symmetric) (OptionRel.symm (related n))

theorem InverseRelated.trans {a b c : Inverse Name Key Value}
    (first : InverseRelated a b) (second : InverseRelated b c) : InverseRelated a c := by
  cases first <;> cases second
  · exact .unit
  · exact .restrict _ _
  · rename_i left middle first right second
    exact .operate _ _ (fun {_ _} inputs => Setoid.trans (first inputs) (second (Setoid.refl _)))
  · exact .retire _

theorem StackRelated.trans {as bs cs : List (Inverse Name Key Value)}
    (first : StackRelated as bs) (second : StackRelated bs cs) : StackRelated as cs := by
  induction first generalizing cs with
  | nil => cases second; exact .nil
  | cons head tail ih =>
    cases second with
    | cons nextHead nextTail => exact .cons (head.trans nextHead) (ih nextTail)

theorem PhaseRelated.trans {Q : Code → Code → Prop} (transitive : ∀ {a b c}, Q a b → Q b c → Q a c)
    {a b c : Phase Name Key Code (Inverse Name Key Value)}
    (first : PhaseRelated Q a b) (second : PhaseRelated Q b c) : PhaseRelated Q a c := by
  cases first with
  | inactive => cases second; exact .inactive
  | reloading view code stack =>
    cases second with
    | reloading _ nextCode nextStack => exact .reloading view (transitive code nextCode) (stack.trans nextStack)
  | active view stack =>
    cases second with
    | active _ nextStack => exact .active view (stack.trans nextStack)
  | unloading view stack =>
    cases second with
    | unloading _ nextStack => exact .unloading view (stack.trans nextStack)

theorem Related.trans {Q : Code → Code → Prop} (transitive : ∀ {a b c}, Q a b → Q b c → Q a c)
    {r s t : R} (first : Related Q r s) (second : Related Q s t) : Related Q r t := by
  intro name
  refine OptionRel.trans (fun a b c (ab : FiberRelated Q a b) (bc : FiberRelated Q b c) => ?_)
    (first name) (second name)
  exact ⟨⟨ab.component.requires.trans bc.component.requires, ab.component.provides.trans bc.component.provides,
    transitive ab.component.entry bc.component.entry⟩, ab.parent.trans bc.parent, ab.retired.trans bc.retired,
    PhaseRelated.trans (Q := Q) (fun h₁ h₂ => transitive h₁ h₂) ab.phase bc.phase, fun key =>
      @OptionRel.trans Value (fun v w => v ≈ w) (fun _ _ _ h₁ h₂ => Setoid.trans h₁ h₂) _ _ _
        (ab.table key) (bc.table key)⟩

theorem OutcomeRelated.symm {a b : Outcome Name Value} (related : OutcomeRelated a b) : OutcomeRelated b a := by
  cases related with
  | unit => exact .unit
  | value h => exact .value (Setoid.symm h)
  | child n => exact .child n

theorem CallbackRelated.symm {a b : Except Error (Value × (Value → Value) × Value)}
    (related : CallbackRelated a b) : CallbackRelated b a := by
  cases a <;> cases b <;> simp_all [CallbackRelated]
  exact ⟨Setoid.symm related.1, (fun {_ _} h => Setoid.symm (related.2.1 (Setoid.symm h))), Setoid.symm related.2.2⟩

theorem ActionRelated.symm {Q : Code → Code → Prop} (symmetric : ∀ a b, Q a b → Q b a)
    {a b : Action Name Key Value Code Error} (related : ActionRelated Q a b) : ActionRelated Q b a := by
  cases related with
  | unit => exact .unit
  | provide key values => exact .provide key (Setoid.symm values)
  | operate key callbacks => exact .operate key (fun a b h => (callbacks b a (Setoid.symm h)).symm)
  | instantiate components => exact .instantiate (components.symm symmetric)

theorem ProgramsRelated.symm {Q : Code → Code → Prop} (symmetric : ∀ a b, Q a b → Q b a)
    {program other : Code → Instruction Name Key Value Code Error}
    (programs : ProgramsRelated Q program other) : ProgramsRelated Q other program := by
  refine ⟨?_, ?_⟩
  · intro a b codes
    exact (programs.action b a (symmetric _ _ codes)).symm symmetric
  · intro a b codes x y outcomes
    exact OptionRel.mono (fun _ _ h => symmetric _ _ h)
      (OptionRel.symm (programs.next b a (symmetric _ _ codes) y x outcomes.symm))

/-- Rule applicability in both directions, for the same rule and actor. This
uses primitive contracts and the proved nine-rule transport, not a bisimulation
assumption. `step_simulation` also gives the related successor for each step. -/
theorem step_applicability_iff {Q : Code → Code → Prop}
    (symmetric : ∀ a b, Q a b → Q b a) (reflexive : ∀ a, Q a a)
    {program other : Code → Instruction Name Key Value Code Error}
    (programs : ProgramsRelated Q program other)
    {rule : Labeled.Rule} {actor : Name} {r s : R} (related : Related Q r s) :
    (∃ r', Labeled.Step program rule actor r r') ↔ (∃ s', Labeled.Step other rule actor s s') := by
  constructor
  · rintro ⟨r', step⟩
    obtain ⟨s', paired, _⟩ := step_simulation programs (fun a => ⟨a, reflexive a⟩) related step
    exact ⟨s', paired⟩
  · rintro ⟨s', step⟩
    obtain ⟨r', paired, _⟩ := step_simulation (programs.symm symmetric)
      (fun a => ⟨a, reflexive a⟩) (related.symm symmetric) step
    exact ⟨r', paired⟩

end Cordis.StageSimulation
