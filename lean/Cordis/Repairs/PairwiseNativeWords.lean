import Cordis.Repairs.PairwiseMixed
import Cordis.Repairs.GuardedTypedCuts

/-! Native witnesses for the recorded mixed-word evaluator. A forward
descriptor carries the selected instruction and route or draw. A saved
descriptor carries the native landing which actually produced its token. -/
namespace Cordis.Repairs.PairwiseNativeWords
open TypedRegistry PairwiseMixed PairwiseSlots PairwiseRegistry PairwiseControl
open PaperEffectEquations (CoeffectOperations)
open PartialCoeffectLifting (PartialMap)
open PartialCoeffectIndependenceContracts (tableSetoid)
open Iterators (OptionRel)
open PairwiseOperations (table_and_route declared_key)

universe u
variable {Name Key Code : Type u} {V : Key → Type u}
variable [DecidableEq Name] [DecidableEq Key] {ops : CoeffectOperations V}
local notation "R" => Registry Name V Code
local notation "SR" => Stamped Name V Code
local notation "I" => Inverse Name V
local notation "M" => MixedEdit Name V Code
local notation "Program" => Code → Instruction Name ops Code

/-- The discrete choices of a reachable forward head. The actual callback
continues to run on the candidate input, returning its own typed result. -/
inductive Forward (program : Program) (actor : Name) (code : Code) where
  | unit : (program code).action = .unit → Forward program actor code
  | provide (key : Key) (value : V key) :
    (program code).action = .provide key value → Forward program actor code
  | operate (owner : Name) (key : Key) (name : ops.Name key) (argument : ops.Argument key name) :
    (program code).action = .operate key name argument → Forward program actor code
  | birth (child : Name) (component : Calculus.Component Key Code) (stamp : Nat) :
    (program code).action = .instantiate component → Forward program actor code

variable {program : Code → Instruction Name ops Code} {actor : Name} {code : Code}

@[simp] private theorem single (letter : M) (before : SR) : runMixed [letter] before = runLetter letter before := by
  change ((runLetter letter before).bind some) = runLetter letter before
  cases runLetter letter before <;> rfl

def Forward.word : Forward program actor code → List M
  | .unit _ => []
  | .provide key value _ => [.inr (.provide actor key value)]
  | .operate owner key name argument _ =>
    [.inr (.operate owner key (PartialCoeffectLifting.forward (ops.operation key name argument)))]
  | .birth child component stamp _ => [.inl (.birth actor child component stamp)]

def Forward.ready (head : Forward program actor code) (state : R) : Prop :=
  match head with
  | .unit _ | .birth .. => True
  | .provide key _ _ => ∃ row, state actor = some row ∧ row.component.provides key = true
  | .operate owner key _ _ _ => bindingOwner state actor key = some owner

def Forward.stamps (head : Forward program actor code) (live : Name → Option Nat) : Name → Option Nat :=
  match head with
  | .birth child _ stamp _ => fun name => if name = child then some stamp else live name
  | _ => live

def Forward.draw (head : Forward program actor code) : Option Name :=
  match head with
  | .birth child _ _ _ => some child
  | _ => none

/-- Reflection retains the real coeffect outcome and capture. The row
declaration and routed owner are explicit parts of the compatible probe. -/
theorem Forward.reify (head : Forward program actor code) {before after : SR}
    (compatible : head.ready before.1) (executed : runMixed head.word before = some after) :
    (∃ token next, Land program actor code before.1 after.1 token next ∧ capturedChild token = head.draw) ∧
      after.2 = head.stamps before.2 := by
  classical
  cases head with
  | unit action =>
    change some before = some after at executed
    cases Option.some.inj executed
    exact ⟨⟨_, _, .unit _ _ _ action, rfl⟩, rfl⟩
  | provide key value action =>
    obtain ⟨row, found, declared⟩ := compatible
    have edits : runOrdinary (.provide actor key value) before = some after := by
      simpa [Forward.word] using executed
    obtain ⟨output, called, result⟩ := Option.map_eq_some_iff.mp edits
    rw [← result]
    exact ⟨⟨_, _, provision_of_run action found declared called, rfl⟩, rfl⟩
  | operate owner key name argument action =>
    have edits : runOrdinary (.operate owner key (PartialCoeffectLifting.forward (ops.operation key name argument)))
        before = some after := by simpa [Forward.word] using executed
    obtain ⟨output, called, result⟩ := Option.map_eq_some_iff.mp edits
    obtain ⟨token, outcome, native⟩ := operation_of_run action compatible called
    rw [← result]
    exact ⟨⟨_, _, native, rfl⟩, rfl⟩
  | birth child component stamp action =>
    simp only [Forward.word, single, runLetter, PairwiseControl.run] at executed
    by_cases ready : Insertable before.1 child component (some actor)
    · simp only [if_pos ready] at executed
      cases Option.some.inj executed
      exact ⟨⟨_, _, .instantiate _ _ _ _ _ action ready, rfl⟩, rfl⟩
    · simp [ready] at executed

/-- A saved generator has a real native source, including its producing
code and the exact token which that source returned. -/
structure Saved (program : Program) (actor : Name) where
  origin : R
  output : R
  code : Code
  token : I
  next : Option Code
  stamp : Nat
  landed : Land program actor code origin output token next

def Saved.word (saved : Saved program actor) : List M :=
  match saved.token with
  | .unit => []
  | .restrict owner key => [.inr (.restrict owner key)]
  | .operate owner key inverse => [.inr (.operate owner key inverse)]
  | .retire child => [.inl (.retire child saved.stamp)]

def Saved.native (saved : Saved program actor) (before after : SR) : Prop :=
  InverseDefined before.1 saved.token ∧ after.2 = before.2 ∧
    encodeRegistry ops after.1 =
      (IncarnationReplay.Capture.mk (encodeInverse ops saved.token) saved.stamp).apply before.2 (encodeRegistry ops before.1)

/-- A recorded inverse reflects to its strict native domain, with actual
incarnation checking and without using a completed callback on failure. -/
theorem Saved.reify (saved : Saved program actor) {before after : SR}
    (executed : runMixed saved.word before = some after) : saved.native before after := by
  cases token : saved.token with
  | unit =>
    simp [Saved.word, token, runMixed] at executed
    subst after
    simp [Saved.native, token, InverseDefined, encodeInverse, IncarnationReplay.Capture.apply, Stages.undo]
  | restrict owner key =>
    have edits : runOrdinary (.restrict owner key) before = some after := by
      simpa [Saved.word, token] using executed
    obtain ⟨output, called, result⟩ := Option.map_eq_some_iff.mp edits
    obtain ⟨defined, equation⟩ := restriction_of_run called
    rw [← result]
    exact ⟨by simpa only [token] using defined, rfl, by
      simp [token, IncarnationReplay.Capture.apply, encodeInverse, equation]⟩
  | operate owner key inverse =>
    have edits : runOrdinary (.operate owner key inverse) before = some after := by
      simpa [Saved.word, token] using executed
    obtain ⟨output, called, result⟩ := Option.map_eq_some_iff.mp edits
    obtain ⟨defined, equation⟩ := operation_inverse_of_run called
    rw [← result]
    exact ⟨by simpa only [token] using defined, rfl, by
      simp [token, IncarnationReplay.Capture.apply, encodeInverse, equation]⟩
  | retire child =>
    have output : after = savedRetire before child saved.stamp := by
      simpa [Saved.word, token, PairwiseControl.run] using executed.symm
    rw [output]
    by_cases test : before.2 child = some saved.stamp <;>
      simp [Saved.native, token, InverseDefined, savedRetire, test, encodeInverse, IncarnationReplay.Capture.apply]

private theorem runLetter_keeps_row {letter : M} {before after : SR} {name : Name} {row : Fiber Name V Code}
    (executed : runLetter letter before = some after) (present : before.1 name = some row) :
    ∃ current, after.1 name = some current ∧ current.component = row.component ∧ current.phase = row.phase := by
  classical
  cases letter with
  | inl control =>
    cases control with
    | birth parent child component stamp =>
      simp only [runLetter, PairwiseControl.run] at executed
      split at executed
      · rename_i ready
        cases Option.some.inj executed
        have distinct : name ≠ child := by
          intro same
          subst name
          have absent := ready.1
          rw [present] at absent
          cases absent
        exact ⟨row, by simpa [addBirth, put, distinct] using present, rfl, rfl⟩
      · contradiction
    | retire child stamp =>
      have result : after = savedRetire before child stamp := (Option.some.inj executed).symm
      rw [result]
      by_cases fires : before.2 child = some stamp
      · by_cases same : name = child
        · subst name
          exact ⟨{ row with retired := true }, by simp [savedRetire, fires, retire, TypedRegistry.modify, present], rfl, rfl⟩
        · exact ⟨row, by simpa [savedRetire, fires, retire, TypedRegistry.modify, same] using present, rfl, rfl⟩
      · exact ⟨row, by simpa [savedRetire, fires] using present, rfl, rfl⟩
  | inr edit =>
    obtain ⟨middle, wrote, same⟩ := Option.map_eq_some_iff.mp (show runOrdinary edit before = some after from executed)
    rw [← same]
    obtain ⟨_, value, _, _, rfl⟩ := edit_success wrote
    by_cases target : name = edit.slot.1
    · subst name
      let updated : Fiber Name V Code := { row with table := fun key =>
        if same : edit.slot.2 = key then same ▸ value else row.table key }
      exact ⟨updated, by simp [updated, write, TypedRegistry.modify, present], rfl, rfl⟩
    · exact ⟨row, by simpa [write, TypedRegistry.modify, target] using present, rfl, rfl⟩

/-- A complete recorded word preserves an existing actor's declarations
and phase. These facts carry the local primitive's native route guard. -/
theorem runMixed_keeps_row {word : List M} {before after : SR} {name : Name} {row : Fiber Name V Code}
    (executed : runMixed word before = some after) (present : before.1 name = some row) :
    ∃ current, after.1 name = some current ∧ current.component = row.component ∧ current.phase = row.phase := by
  induction word generalizing before row with
  | nil =>
    change some before = some after at executed
    cases Option.some.inj executed
    exact ⟨row, present, rfl, rfl⟩
  | cons head rest ih =>
    obtain ⟨middle, first, remaining⟩ := Option.bind_eq_some_iff.mp executed
    obtain ⟨entry, found, component, phase⟩ := runLetter_keeps_row (letter := head) first present
    obtain ⟨current, foundAfter, cmp, next⟩ := ih remaining found
    exact ⟨current, foundAfter, cmp.trans component, next.trans phase⟩

/-- Every new row in a successful word comes from a recorded birth at its
name with its actual immutable component. -/
theorem runMixed_birth_of_new_row {word : List M} {before after : SR} {name : Name}
    {row : Fiber Name V Code} (executed : runMixed word before = some after)
    (vacant : before.1 name = none) (present : after.1 name = some row) :
    ∃ parent stamp, Control.birth parent name row.component stamp ∈ controlPart word := by
  induction word generalizing before with
  | nil =>
    change some before = some after at executed
    cases Option.some.inj executed
    rw [vacant] at present
    cases present
  | cons head tail ih =>
    obtain ⟨middle, first, remaining⟩ := Option.bind_eq_some_iff.mp executed
    cases newRow : middle.1 name with
    | none =>
      obtain ⟨parent, stamp, member⟩ := ih remaining newRow
      refine ⟨parent, stamp, ?_⟩
      cases head with
      | inl control => exact List.mem_cons_of_mem control member
      | inr _ => exact member
    | some entry =>
      obtain ⟨current, found, component, _⟩ := runMixed_keeps_row remaining newRow
      have same := Option.some.inj (found.symm.trans present)
      subst current
      cases head with
      | inl control =>
        cases control with
        | retire child stamp =>
          change some (savedRetire before child stamp) = some middle at first
          cases Option.some.inj first
          by_cases fires : before.2 child = some stamp <;> by_cases target : name = child <;>
            simp_all [savedRetire, retire, TypedRegistry.modify]
        | birth parent child payload stamp =>
          simp only [runLetter, PairwiseControl.run] at first
          split at first
          · cases Option.some.inj first
            by_cases target : name = child
            · subst child
              have entryEq : fresh payload (some parent) = entry := by simpa [addBirth, put] using newRow
              subst entry
              change row.component = payload at component
              exact ⟨parent, stamp, by simp [controlPart, component]⟩
            · simp [addBirth, put, target, vacant] at newRow
          · contradiction
      | inr edit =>
        obtain ⟨output, wrote, rfl⟩ := Option.map_eq_some_iff.mp
          (show runOrdinary edit before = some middle from first)
        obtain ⟨_, value, _, _, rfl⟩ := edit_success wrote
        by_cases target : name = edit.slot.1 <;> simp_all [write, TypedRegistry.modify]

theorem Forward.ready_after_word (head : Forward program actor code) {before after : SR} {word : List M}
    (ready : head.ready before.1) (executed : runMixed word before = some after) : head.ready after.1 := by
  cases head with
  | unit _ | birth _ _ _ _ => exact True.intro
  | provide key value action =>
    obtain ⟨row, found, declared⟩ := ready
    obtain ⟨current, foundAfter, component, _⟩ := runMixed_keeps_row executed found
    exact ⟨current, foundAfter, by simpa [component] using declared⟩
  | operate owner key name argument action =>
    cases present : before.1 actor with
    | none =>
      change bindingOwner before.1 actor key = some owner at ready
      simp [bindingOwner, present] at ready
    | some row =>
      obtain ⟨current, found, component, phase⟩ := runMixed_keeps_row executed present
      change bindingOwner after.1 actor key = some owner
      change bindingOwner before.1 actor key = some owner at ready
      simpa [bindingOwner, found, component, phase] using (show
        (if row.component.provides key then some actor else if row.component.requires key then
          row.phase.committed.map (fun view => view key) else none) = some owner from by
            simpa [bindingOwner, present] using ready)

private theorem Forward.ready_before_word (head : Forward program actor code) {before after : SR} {word : List M}
    {row : Fiber Name V Code} (present : before.1 actor = some row)
    (executed : runMixed word before = some after) (ready : head.ready after.1) : head.ready before.1 := by
  obtain ⟨current, found, component, phase⟩ := runMixed_keeps_row executed present
  cases head with
  | unit _ | birth _ _ _ _ => exact True.intro
  | provide key value action =>
    obtain ⟨entry, entryFound, declared⟩ := ready
    cases Option.some.inj (entryFound.symm.trans found)
    exact ⟨row, present, by simpa only [component] using declared⟩
  | operate owner key name argument action =>
    change bindingOwner before.1 actor key = some owner
    change bindingOwner after.1 actor key = some owner at ready
    simpa [bindingOwner, present] using (show
      (if row.component.provides key then some actor else if row.component.requires key then
        row.phase.committed.map (fun view => view key) else none) = some owner from by
          simpa [bindingOwner, found, component, phase] using ready)

/-- Read the fixed descriptor directly from the native landing. This keeps
the actual route, declared child component, original draw and selected
birth stamp. -/
theorem Forward.record {before : SR} {after : R} {token : I} {next : Option Code}
    (landed : Land program actor code before.1 after token next) (stamp : Nat) :
    ∃ head : Forward program actor code, head.ready before.1 ∧ capturedChild token = head.draw ∧
      runMixed head.word before = some (after, head.stamps before.2) ∧
      ∀ child payload born, Control.birth actor child payload born ∈ controlPart head.word → born = stamp := by
  classical
  cases landed with
  | unit _ _ _ action => exact ⟨.unit action, trivial, rfl, rfl, by simp [Forward.word, controlPart]⟩
  | provide _ _ _ row key value action found declared empty =>
    refine ⟨.provide key value action, ⟨row, found, declared⟩, rfl, ?_, by simp [Forward.word, controlPart]⟩
    simp [Forward.word, Forward.stamps, runOrdinary, runEdit, Edit.slot, Edit.apply, tablesOf, tableAt, found, empty]
  | operate _ _ _ key name arg owner input output inverse result action located called =>
    obtain ⟨route, bound⟩ := table_and_route located
    obtain ⟨holder, found⟩ : ∃ holder, before.1 owner = some holder := by
      cases row : before.1 owner with
      | none => simp [tableAt, row] at bound
      | some holder => exact ⟨holder, rfl⟩
    refine ⟨.operate owner key name arg action, route, rfl, ?_, by simp [Forward.word, controlPart]⟩
    simp [Forward.word, Forward.stamps, runOrdinary, runEdit, tablesOf, Edit.slot, Edit.apply,
      found, bound, PartialCoeffectLifting.forward, called]
  | instantiate _ _ _ component child action ready =>
    refine ⟨.birth child component stamp action, trivial, rfl, ?_, ?_⟩
    · simp [Forward.word, Forward.stamps, PairwiseControl.run, addBirth, ready]
    · intro name declared born member
      simp [Forward.word, controlPart] at member
      exact member.2.2

/-- Record exactly the supplied native inverse at its strict replay probe.
The recorded operation uses its original partial function and the child
retirement keeps the original capture stamp. -/
theorem Saved.record (saved : Saved program actor) {before after : SR}
    (actual : saved.native before after) : runMixed saved.word before = some after := by
  obtain ⟨defined, live, output⟩ := actual
  cases token : saved.token with
  | unit =>
    have same : after.1 = before.1 := encodeRegistry_injective ops (by
      simpa [token, encodeInverse, IncarnationReplay.Capture.apply, Stages.undo] using output)
    simpa [Saved.word, token, runMixed] using congrArg some (Prod.ext same live).symm
  | restrict owner key =>
    have bound : tableAt before.1 owner key ≠ none := by simpa only [token, InverseDefined] using defined
    have same : after.1 = write before.1 owner key none := encodeRegistry_injective ops (by
      simpa [token, encodeInverse, IncarnationReplay.Capture.apply, Stages.undo] using output)
    cases present : before.1 owner with
    | none => simp [tableAt, present] at bound
    | some row =>
      cases cell : row.table key with
      | none => exact False.elim (bound (by simp [tableAt, present, cell]))
      | some value =>
        simp [Saved.word, token, runOrdinary, runEdit, Edit.slot, Edit.apply, tablesOf, tableAt, present, cell]
        exact Prod.ext same.symm live.symm
  | operate owner key inverse =>
    rcases (show ∃ input output, tableAt before.1 owner key = some input ∧ inverse input = some output from by
      simpa only [token, InverseDefined] using defined) with ⟨input, changed, bound, called⟩
    have same : after.1 = undo (.operate owner key inverse) before.1 := encodeRegistry_injective ops (by
      simpa [token, encodeInverse, IncarnationReplay.Capture.apply] using output)
    rw [PairwiseOperations.undo_operate_eq_write bound called] at same
    cases present : before.1 owner with
    | none => simp [tableAt, present] at bound
    | some row =>
      simp [Saved.word, token, runOrdinary, runEdit, Edit.slot, Edit.apply, tablesOf, present, bound, called]
      exact Prod.ext same.symm live.symm
  | retire child =>
    have same : after = savedRetire before child saved.stamp := by
      by_cases test : before.2 child = some saved.stamp
      · simp only [savedRetire, if_pos test]
        apply Prod.ext
        · exact encodeRegistry_injective ops (by simpa [token, encodeInverse, IncarnationReplay.Capture.apply, test] using output)
        · exact live
      · simp only [savedRetire, if_neg test]
        apply Prod.ext _ live
        exact encodeRegistry_injective ops (by simpa [token, encodeInverse, IncarnationReplay.Capture.apply, test] using output)
    simp [Saved.word, token, PairwiseControl.run, same]

/-- The descriptor of an admitted native landing runs that exact landing.
In a bound operation the descriptor's route is determined by the probe. -/
theorem Forward.run_of_landing (head : Forward program actor code) {before after : SR}
    {token : I} {next : Option Code}
    (landed : Land program actor code before.1 after.1 token next) (ready : head.ready before.1)
    (drawn : capturedChild token = head.draw) (stamps : after.2 = head.stamps before.2) :
    runMixed head.word before = some after := by
  obtain ⟨registry, live⟩ := after
  cases landed with
  | unit _ _ _ action =>
    cases head with
    | unit _ => exact congrArg some (Prod.ext rfl stamps.symm)
    | provide _ _ instructed | operate _ _ _ _ instructed | birth _ _ _ instructed => simp_all
  | provide _ _ _ row key value action present declared empty =>
    cases head with
    | unit instructed | operate _ _ _ _ instructed | birth _ _ _ instructed => simp_all
    | provide otherKey otherValue instructed =>
      injection action.symm.trans instructed with sameKey sameValue
      subst otherKey
      cases sameValue
      simp [Forward.word, runOrdinary, runEdit, tablesOf, tableAt, Edit.slot, Edit.apply, present, empty]
      exact ⟨rfl, stamps.symm⟩
  | operate _ _ _ key name argument owner input output inverse reply action located returned =>
    cases head with
    | unit instructed | provide _ _ instructed | birth _ _ _ instructed => simp_all
    | operate otherOwner otherKey otherName otherArgument instructed =>
      obtain ⟨route, bound⟩ := table_and_route located
      injection action.symm.trans instructed with sameKey sameName sameArgument
      subst otherKey
      cases sameName
      cases sameArgument
      have ownerEq : owner = otherOwner := Option.some.inj (route.symm.trans ready)
      subst otherOwner
      cases present : before.1 owner with
      | none => simp [tableAt, present] at bound
      | some holder =>
        simp [Forward.word, runOrdinary, runEdit, tablesOf, Edit.slot, Edit.apply, present, bound,
          PartialCoeffectLifting.forward, returned]
        exact ⟨rfl, stamps.symm⟩
  | instantiate _ _ _ childComponent child action insertable =>
    cases head with
    | unit instructed | provide _ _ instructed | operate _ _ _ _ instructed => simp_all
    | birth otherChild otherComponent stamp instructed =>
      cases Action.instantiate.inj (action.symm.trans instructed)
      have childEq : child = otherChild := by simpa [capturedChild, Forward.draw] using drawn
      subst otherChild
      simp [Forward.word, PairwiseControl.run, insertable]
      exact Prod.ext rfl stamps.symm

inductive Letter (program : Program) (actor : Name) where
  | advance (code : Code) (head : Forward program actor code)
  | replay (saved : Saved program actor)

def Letter.word : Letter program actor → List M
  | .advance _ head => head.word
  | .replay saved => saved.word

def Letter.ready (letter : Letter program actor) (state : R) : Prop :=
  match letter with
  | .advance _ head => head.ready state
  | .replay _ => True

inductive Reply (Name : Type u) {Key : Type u} {V : Key → Type u}
    (ops : CoeffectOperations V) (Code : Type u) where
  | advance (token : Inverse Name V) (next : Option Code) (outcome : Outcome Name ops)
  | replay

local notation "ReplyT" => Reply Name ops Code

def Letter.Native (letter : Letter program actor) (before after : SR) (reply : ReplyT) : Prop :=
  match letter, reply with
  | .advance code head, .advance token next outcome => Land program actor code before.1 after.1 token next ∧
      capturedChild token = head.draw ∧ after.2 = head.stamps before.2 ∧ head.ready before.1 ∧
      replyAt program actor head.draw code before.1 = some outcome
  | .replay saved, .replay => saved.native before after
  | _, _ => False

def Reply.Related (observe : ∀ key, Setoid (V key)) : ReplyT → ReplyT → Prop
  | .advance first next outcome, .advance second otherNext otherOutcome =>
    next = otherNext ∧ PairwiseForward.CaptureRelated observe first second ∧ outcome = otherOutcome
  | .replay, .replay => True
  | _, _ => False

/-- A successful child reply supplies the actual initial fiber of that
child. Its component is the one declared by the executing instruction. -/
theorem Letter.child_payload (head : Forward program actor code)
    {before after : SR} {token : I} {next : Option Code} {child : Name}
    (native : (Letter.advance code head).Native before after (.advance token next (.child child))) :
    ∃ component, (program code).action = .instantiate component ∧
      after.1 child = some (fresh component (some actor)) := by
  rcases before with ⟨before, live⟩
  rcases after with ⟨after, newLive⟩
  obtain ⟨landed, drawn, _, _, replied⟩ := native
  change Land program actor code before after token next at landed
  change replyAt program actor head.draw code before = some (.child child) at replied
  cases landed with
  | unit _ _ _ action => simp [replyAt, action] at replied
  | provide _ _ _ _ _ _ action _ _ _ => simp [replyAt, action] at replied
  | operate _ _ _ _ _ _ _ _ _ _ _ action located called =>
    simp [replyAt, action, located, called] at replied
  | instantiate _ _ _ component newborn action ready =>
    change capturedChild (.retire newborn : I) = head.draw at drawn
    have chosen : some newborn = some child := by simpa [← drawn, replyAt, action, capturedChild] using replied
    cases Option.some.inj chosen
    exact ⟨component, action, by simp [put]⟩

theorem Letter.reify (letter : Letter program actor) {before after : SR}
    (ready : letter.ready before.1) (executed : runMixed letter.word before = some after) :
    ∃ reply, letter.Native before after reply := by
  cases letter with
  | advance code head =>
    obtain ⟨⟨token, next, actual, draw⟩, stamps⟩ := head.reify ready executed
    obtain ⟨outcome, replied, _⟩ := actual.reply
    exact ⟨.advance token next outcome, actual, draw, stamps, ready, by simpa only [draw] using replied⟩
  | replay saved => exact ⟨.replay, saved.reify executed⟩

theorem Letter.record_native (letter : Letter program actor) {before after : SR} {reply : ReplyT}
    (native : letter.Native before after reply) : runMixed letter.word before = some after := by
  cases letter with
  | replay saved =>
    cases reply with
    | replay => exact saved.record native
    | advance => exact False.elim native
  | advance selectedCode head =>
    cases reply with
    | replay => exact False.elim native
    | advance =>
      obtain ⟨landed, drawn, stamps, ready, _⟩ := native
      exact head.run_of_landing landed ready drawn stamps

theorem typed_landing_deterministic {before left right : R} {first second : I} {next otherNext : Option Code}
    (a : Land program actor code before left first next) (b : Land program actor code before right second otherNext)
    (draws : capturedChild first = capturedChild second) : left = right ∧ first = second ∧ next = otherNext := by
  have sameDraw (child : Name) (selected : encodeInverse ops first = .retire child) :
      encodeInverse ops second = .retire child := by
    have fixed : first = .retire child := by cases first <;> simp_all [encodeInverse]
    rw [fixed] at draws
    have other : second = .retire child := by cases second <;> simp_all [capturedChild]
    simp [other, encodeInverse]
  obtain ⟨states, tokens, branch⟩ := GuardedLandingMatching.landing_deterministic_at_draw
    (land_encode ops a) (land_encode ops b) sameDraw
  exact ⟨encodeRegistry_injective ops states, encodeInverse_injective ops tokens, branch⟩

omit [DecidableEq Name] [DecidableEq Key] in
private theorem transport_keeps_draw {observe : ∀ key, Setoid (V key)} {original paired : I}
    (relation : PairwiseForward.CaptureRelated observe original paired) : capturedChild original = capturedChild paired := by
  cases relation <;> rfl

/-- The same recorded letter on related probes preserves the selected
code and relates the actual typed partial inverses before encoding. -/
theorem Letter.pair_yields (observe : ∀ key, Setoid (V key))
    (respect : ∀ key, PaperObservationEquations.OperationRespects ops key (observe key).r)
    (letter : Letter program actor) {left right first second : SR} {firstReply secondReply : ReplyT}
    (sources : StampedRelated ops observe left right)
    (leftApplication : letter.Native left first firstReply) (rightApplication : letter.Native right second secondReply) :
    Reply.Related observe firstReply secondReply := by
  cases letter with
  | replay saved => cases firstReply <;> cases secondReply <;> simp_all [Native, Reply.Related]
  | advance code head =>
    cases firstReply with
    | replay => exact False.elim leftApplication
    | advance token chosen outcome =>
      cases secondReply with
      | replay => exact False.elim rightApplication
      | advance otherToken otherChosen otherOutcome =>
        obtain ⟨leftNative, leftDraw, _, _, leftReply⟩ := leftApplication
        obtain ⟨rightNative, rightDraw, _, _, rightReply⟩ := rightApplication
        obtain ⟨moved, captured, transferred, _, observes, sameReply⟩ := PairwisePrograms.transport_landing observe program respect
          sources.2 leftNative
        have draws := (transport_keeps_draw observes).symm.trans (leftDraw.trans rightDraw.symm)
        obtain ⟨_, rfl, same⟩ := typed_landing_deterministic transferred rightNative draws
        rw [leftDraw, rightDraw, leftReply, rightReply] at sameReply
        exact ⟨same, observes, Option.some.inj sameReply⟩

def words (script : List (Letter program actor)) : List M := script.flatMap Letter.word

inductive NativePath (program : Program) (actor : Name) : List (Letter program actor) → SR → SR → List ReplyT → Prop where
  | nil (state : SR) : NativePath program actor [] state state []
  | cons {letter : Letter program actor} {tail : List (Letter program actor)} {before middle after : SR} {reply replies} :
    letter.Native before middle reply → NativePath program actor tail middle after replies →
    NativePath program actor (letter :: tail) before after (reply :: replies)

theorem split_word (left right : List M) (state : SR) :
    runMixed (left ++ right) state = (runMixed left state).bind (runMixed right) := by
  simp only [runMixed, List.map_append, PartialReplayHistory.run_append]

theorem NativePath.record {script : List (Letter program actor)} {before after : SR} {replies : List ReplyT}
    (path : NativePath program actor script before after replies) : runMixed (words script) before = some after := by
  induction path with
  | nil => rfl
  | @cons letter tail before middle after reply replies landed remaining ih =>
    change runMixed (letter.word ++ words tail) before = some after
    simpa [split_word, letter.record_native landed] using ih

theorem Letter.ready_of_native (letter : Letter program actor) {before after : SR} {reply : ReplyT}
    (landed : letter.Native before after reply) : letter.ready before.1 := by
  cases letter with
  | replay _ => exact True.intro
  | advance code head =>
    cases reply with
    | replay => exact False.elim landed
    | advance => exact landed.2.2.2.1

theorem NativePath.ready {script : List (Letter program actor)} {before after : SR} {replies : List ReplyT}
    {row : Fiber Name V Code} (found : before.1 actor = some row)
    (path : NativePath program actor script before after replies) : ∀ letter ∈ script, letter.ready before.1 := by
  induction path generalizing row with
  | nil => simp
  | @cons head tail before middle after reply replies landed remaining ih =>
    intro letter member
    rcases List.mem_cons.mp member with rfl | later
    · exact letter.ready_of_native landed
    · have executed := head.record_native landed
      obtain ⟨entry, atCut, _, _⟩ := runMixed_keeps_row executed found
      have laterReady := ih atCut letter later
      cases letter with
      | replay _ => exact True.intro
      | advance code nextHead => exact nextHead.ready_before_word found executed laterReady

private theorem Letter.reply_eq (letter : Letter program actor) {before first second : SR} {left right : ReplyT}
    (original : letter.Native before first left) (other : letter.Native before second right) : left = right := by
  cases letter with
  | replay saved => cases left <;> cases right <;> simp_all [Native]
  | advance code head =>
    cases left with
    | replay => exact False.elim original
    | advance token next outcome =>
      cases right with
      | replay => exact False.elim other
      | advance otherToken otherNext otherOutcome =>
        obtain ⟨_, rfl, rfl⟩ := typed_landing_deterministic original.1 other.1 (original.2.1.trans other.2.1.symm)
        cases Option.some.inj (original.2.2.2.2.symm.trans other.2.2.2.2)
        rfl

theorem NativePath.replies_eq {script : List (Letter program actor)} {before first second : SR}
    {left right : List ReplyT} (original : NativePath program actor script before first left)
    (other : NativePath program actor script before second right) : left = right := by
  induction original generalizing second right with
  | nil => cases other; rfl
  | @cons head tail before middle first reply replies landed remaining ih =>
    cases other with
    | @cons _ _ _ otherMiddle _ otherReply otherReplies otherLand otherRemaining =>
      have sameCut := Option.some.inj ((head.record_native landed).symm.trans (head.record_native otherLand))
      subst otherMiddle
      rw [head.reply_eq landed otherLand, ih otherRemaining]

theorem Letter.ready_after_word (letter : Letter program actor) {before after : SR} {word : List M}
    (originally : letter.ready before.1) (executed : runMixed word before = some after) :
    letter.ready after.1 := by
  cases letter with
  | advance _ moving => exact moving.ready_after_word originally executed
  | replay _ => exact True.intro

theorem Letter.ready_related (letter : Letter program actor) {observe : ∀ key, Setoid (V key)}
    {before after : R} (related : PairwisePrograms.Related (ops := ops) observe before after)
    (ready : letter.ready before) : letter.ready after := by
  cases letter with
  | replay => trivial
  | advance _ head =>
    cases head with
    | unit | birth => trivial
    | provide key value action =>
      obtain ⟨row, present, declared⟩ := ready
      obtain ⟨other, otherAt, payload⟩ := PairwisePrograms.related_component related present
      exact ⟨other, otherAt, payload.symm ▸ declared⟩
    | operate owner key name argument action =>
      change bindingOwner before actor key = some owner at ready
      exact (PairwisePrograms.related_bindingOwner related actor key).symm.trans ready

/-- Saved moves use the acting component at the actual capture origin.
This is independent of the current row used to run a forward move. -/
def Letter.origin_has (letter : Letter program actor) (component : Calculus.Component Key Code) : Prop :=
  match letter with
  | .advance .. => True
  | .replay saved => ∃ row, saved.origin actor = some row ∧ row.component = component

theorem Letter.admitted (letter : Letter program actor) {before : R}
    {component : Calculus.Component Key Code} {row : Fiber Name V Code}
    (found : before actor = some row) (payload : row.component = component)
    (ready : letter.ready before) (origin : letter.origin_has component) :
    ∀ edit ∈ ordinaryPart letter.word, Admitted ops actor component edit := by
  intro edit member
  cases letter with
  | advance headCode head =>
    cases head with
    | unit _ | birth _ _ _ _ => exact False.elim (List.not_mem_nil member)
    | provide key value _ =>
      cases List.mem_singleton.mp member
      obtain ⟨provider, present, declared⟩ := ready
      cases Option.some.inj (present.symm.trans found)
      exact ⟨rfl, payload ▸ declared⟩
    | operate owner key name argument _ =>
      cases List.mem_singleton.mp member
      exact ⟨payload ▸ PairwiseOperations.declared_route found ready, name, argument, .forward⟩
  | replay saved =>
    obtain ⟨sourceRow, source, sourcePayload⟩ := origin
    obtain ⟨savedOrigin, output, savedCode, token, next, stamp, landed⟩ := saved
    cases landed with
    | unit | instantiate => exact False.elim (List.not_mem_nil member)
    | provide _ _ _ provider key value action present declared empty =>
      cases List.mem_singleton.mp member
      cases Option.some.inj (present.symm.trans source)
      exact ⟨rfl, sourcePayload ▸ declared⟩
    | operate _ _ _ key name argument owner input changed inverse outcome action located returned =>
      cases List.mem_singleton.mp member
      exact ⟨sourcePayload ▸ declared_key source located, name, argument, .inverse input changed inverse outcome returned⟩

theorem script_admitted (script : List (Letter program actor)) {before : R}
    {component : Calculus.Component Key Code} {row : Fiber Name V Code}
    (found : before actor = some row) (payload : row.component = component)
    (ready : ∀ letter ∈ script, Letter.ready letter before)
    (origins : ∀ letter ∈ script, Letter.origin_has letter component) :
    ∀ edit ∈ ordinaryPart (words script), Admitted ops actor component edit := by
  intro edit member
  obtain ⟨mixed, belongs, picked⟩ := List.mem_filterMap.mp member
  obtain ⟨letter, inScript, inLetter⟩ := List.mem_flatMap.mp belongs
  exact letter.admitted found payload (ready letter inScript) (origins letter inScript) edit
    (List.mem_filterMap.mpr ⟨mixed, inLetter, picked⟩)

theorem native_word_of_run (script : List (Letter program actor)) {before after : SR}
    {component : Calculus.Component Key Code} {row : Fiber Name V Code}
    (found : before.1 actor = some row) (payload : row.component = component)
    (ready : ∀ letter ∈ script, Letter.ready letter before.1)
    (origins : ∀ letter ∈ script, Letter.origin_has letter component)
    (executed : runMixed (words script) before = some after) :
    NativeWord program actor component before.1 after.1 := by
  induction script generalizing before row with
  | nil =>
    change some before = some after at executed
    cases Option.some.inj executed
    exact .nil _
  | cons head tail ih =>
    change runMixed (head.word ++ words tail) before = some after at executed
    rw [split_word] at executed
    obtain ⟨middle, first, remaining⟩ := Option.bind_eq_some_iff.mp executed
    have current : NativeMove program actor component before.1 middle.1 := by
      cases head with
      | advance headCode forward =>
        obtain ⟨⟨token, next, landed, _⟩, _⟩ := forward.reify (ready _ List.mem_cons_self) first
        exact .forward found payload landed
      | replay saved =>
        obtain ⟨sourceRow, source, actualComponent⟩ := origins _ List.mem_cons_self
        obtain ⟨defined, _, applied⟩ := saved.reify first
        exact .inverse before.2 saved.stamp source actualComponent saved.landed defined applied
    obtain ⟨currentRow, atCut, currentPayload, _⟩ := runMixed_keeps_row first found
    exact .cons current (ih atCut (currentPayload.trans payload)
      (fun letter member => letter.ready_after_word (ready letter (List.mem_cons_of_mem _ member)) first)
      (fun letter member => origins letter (List.mem_cons_of_mem _ member)) remaining)

/-- Moving a native letter through a successful foreign word preserves
its actual reply. The final probe may also be replaced by a related one,
as happens when comparing the two orders of the prefixes. -/
theorem Letter.pair_yields_after_foreign (observe : ∀ key, Setoid (V key))
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, PaperObservationEquations.OperationRespects ops key (observe key).r)
    {foreignActor : Name} {foreignComponent : Calculus.Component Key Code}
    (different : actor ≠ foreignActor) (letter : Letter program actor)
    {before foreignEnd reordered first second : SR} {row : Fiber Name V Code} {firstReply secondReply : ReplyT}
    (found : before.1 actor = some row) (separate : Transposition.Separated row.component foreignComponent)
    (foreign : NativeWord program foreignActor foreignComponent before.1 foreignEnd.1)
    (related : StampedRelated ops observe foreignEnd reordered)
    (births : ∀ child payload stamp, Control.birth actor child payload stamp ∈ controlPart letter.word →
      ∀ name entry, before.1 name = none → foreignEnd.1 name = some entry →
      PairwiseAllocation.DrawCompatible child name payload entry.component)
    (original : letter.Native before first firstReply) (moved : letter.Native reordered second secondReply) :
    Reply.Related observe firstReply secondReply := by
  cases letter with
  | replay saved => cases firstReply <;> cases secondReply <;> simp_all [Native, Reply.Related]
  | advance headCode head =>
    cases firstReply with
    | replay => exact False.elim original
    | advance token next outcome =>
      cases secondReply with
      | replay => exact False.elim moved
      | advance otherToken otherNext otherOutcome =>
        obtain ⟨landed, draw, _, _, beforeReply⟩ := original
        obtain ⟨landedOther, otherDraw, _, _, afterReply⟩ := moved
        have compatible {drawn payload} (retiring : token = .retire drawn)
            (action : (program headCode).action = .instantiate payload) :
            ∀ name entry, before.1 name = none → foreignEnd.1 name = some entry →
            PairwiseAllocation.DrawCompatible drawn name payload entry.component := by
          subst token
          cases head with
          | unit _ | provide _ _ _ | operate _ _ _ _ _ => simp [capturedChild, Forward.draw] at draw
          | birth child component stamp instructed =>
            have same := Action.instantiate.inj (action.symm.trans instructed)
            subst component
            have sameChild : drawn = child := by simpa [capturedChild, Forward.draw] using draw
            subst child
            exact births drawn payload stamp (by simp [Letter.word, Forward.word, controlPart])
        obtain ⟨afterForeign, newToken, newLand, newCapture, foreignReply⟩ :=
          rerun_after_native_word observe laws found different separate landed foreign (fun _ _ => compatible)
        obtain ⟨afterTransport, transported, transportedLand, _, transportedCapture, transportReply⟩ :=
          PairwisePrograms.transport_landing observe program respect related.2 newLand
        have captures := (newCapture.symm).trans transportedCapture
        have sameDraw := (transport_keeps_draw captures).symm.trans (draw.trans otherDraw.symm)
        obtain ⟨_, rfl, branch⟩ := typed_landing_deterministic transportedLand landedOther sameDraw
        have sameReply := foreignReply.trans transportReply
        rw [draw, otherDraw, beforeReply, afterReply] at sameReply
        exact ⟨branch, captures, Option.some.inj sameReply⟩

/-- Reflect a successful finite evaluation to genuine native steps.
Every intermediate provider route and declaration guard persists from the
common probe. Partial inverse success is derived at the point of replay. -/
theorem reify_path (script : List (Letter program actor)) {before after : SR}
    (ready : ∀ letter ∈ script, Letter.ready letter before.1)
    (executed : runMixed (words script) before = some after) : ∃ replies, NativePath program actor script before after replies := by
  induction script generalizing before with
  | nil =>
    change some before = some after at executed
    cases Option.some.inj executed
    exact ⟨[], .nil _⟩
  | cons head tail ih =>
    change runMixed (head.word ++ words tail) before = some after at executed
    rw [split_word] at executed
    obtain ⟨middle, first, remaining⟩ := Option.bind_eq_some_iff.mp executed
    obtain ⟨reply, native⟩ := head.reify (ready head List.mem_cons_self) first
    have tailReady : ∀ letter ∈ tail, Letter.ready letter middle.1 := by
      intro letter member
      exact letter.ready_after_word (ready letter (List.mem_cons_of_mem _ member)) first
    obtain ⟨replies, later⟩ := ih tailReady remaining
    exact ⟨reply :: replies, .cons native later⟩

inductive RepliesRelated (observe : ∀ key, Setoid (V key)) : List ReplyT → List ReplyT → Prop where
  | nil : RepliesRelated observe [] []
  | cons {first second : ReplyT} {left right : List ReplyT} :
    Reply.Related observe first second → RepliesRelated observe left right →
    RepliesRelated observe (first :: left) (second :: right)

/-- Successful evaluations of the same script on structurally related
probes keep every selected continuation and relate the actual captures. -/
theorem paired_reify_path (observe : ∀ key, Setoid (V key))
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops
      (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, PaperObservationEquations.OperationRespects ops key (observe key).r)
    (script : List (Letter program actor)) {component : Calculus.Component Key Code}
    (allowed : ∀ edit ∈ ordinaryPart (words script), Admitted ops actor component edit)
    {left right first second : SR} (sources : StampedRelated ops observe left right)
    (leftReady : ∀ letter ∈ script, Letter.ready letter left.1)
    (rightReady : ∀ letter ∈ script, Letter.ready letter right.1)
    (leftRun : runMixed (words script) left = some first)
    (rightRun : runMixed (words script) right = some second) :
    ∃ leftReplies rightReplies,
      NativePath program actor script left first leftReplies ∧
      NativePath program actor script right second rightReplies ∧ RepliesRelated observe leftReplies rightReplies := by
  induction script generalizing left right with
  | nil =>
    change some left = some first at leftRun
    change some right = some second at rightRun
    cases Option.some.inj leftRun
    cases Option.some.inj rightRun
    exact ⟨[], [], .nil _, .nil _, .nil⟩
  | cons head tail ih =>
    change runMixed (head.word ++ words tail) left = some first at leftRun
    change runMixed (head.word ++ words tail) right = some second at rightRun
    rw [split_word] at leftRun rightRun
    obtain ⟨leftCut, leftHead, leftTail⟩ := Option.bind_eq_some_iff.mp leftRun
    obtain ⟨rightCut, rightHead, rightTail⟩ := Option.bind_eq_some_iff.mp rightRun
    obtain ⟨reply, leftNative⟩ := head.reify (leftReady head List.mem_cons_self) leftHead
    obtain ⟨otherReply, rightNative⟩ := head.reify (rightReady head List.mem_cons_self) rightHead
    have headAllowed (edit) (member : edit ∈ ordinaryPart head.word) := allowed edit (by
      change edit ∈ ordinaryPart (head.word ++ words tail)
      simpa only [ordinaryPart, List.filterMap_append] using List.mem_append_left _ member)
    have tailAllowed (edit) (member : edit ∈ ordinaryPart (words tail)) := allowed edit (by
      change edit ∈ ordinaryPart (head.word ++ words tail)
      simpa only [ordinaryPart, List.filterMap_append] using List.mem_append_right _ member)
    have cutRelation := mixed_respects ops observe laws head.word headAllowed sources
    rw [leftHead, rightHead] at cutRelation
    obtain ⟨leftReplies, rightReplies, leftLater, rightLater, compared⟩ := ih tailAllowed cutRelation
      (fun letter member => letter.ready_after_word (leftReady letter (List.mem_cons_of_mem _ member)) leftHead)
      (fun letter member => letter.ready_after_word (rightReady letter (List.mem_cons_of_mem _ member)) rightHead)
      leftTail rightTail
    exact ⟨reply :: leftReplies, otherReply :: rightReplies, .cons leftNative leftLater,
      .cons rightNative rightLater, .cons (head.pair_yields observe respect sources leftNative rightNative) compared⟩

/-- Compare every native reply in an original script to its reply after
the foreign script. At each local cut the foreign script can also run
from that cut, and its endpoint relates to the corresponding moved cut. -/
theorem pair_script_after_foreign (observe : ∀ key, Setoid (V key))
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, PaperObservationEquations.OperationRespects ops key (observe key).r)
    {foreignActor : Name} {component foreignComponent : Calculus.Component Key Code}
    (different : actor ≠ foreignActor) (separate : Transposition.Separated component foreignComponent)
    (script : List (Letter program actor)) (foreign : List (Letter program foreignActor))
    {before foreignAfter reordered first second : SR} {row foreignRow : Fiber Name V Code}
    (found : before.1 actor = some row) (payload : row.component = component)
    (foreignFound : before.1 foreignActor = some foreignRow) (foreignPayload : foreignRow.component = foreignComponent)
    (allowed : ∀ edit ∈ ordinaryPart (words script), Admitted ops actor component edit)
    (foreignAllowed : ∀ edit ∈ ordinaryPart (words foreign), Admitted ops foreignActor foreignComponent edit)
    (ready : ∀ letter ∈ script, Letter.ready letter before.1)
    (movedReady : ∀ letter ∈ script, Letter.ready letter reordered.1)
    (foreignReady : ∀ letter ∈ foreign, Letter.ready letter before.1)
    (foreignOrigins : ∀ letter ∈ foreign, Letter.origin_has letter foreignComponent)
    (births : ∀ control ∈ controlPart (words script),
      ∀ other ∈ controlPart (words foreign), Compatible control other)
    (self : StampedRelated ops observe before before)
    (paired : StampedRelated ops observe foreignAfter reordered)
    (foreignRun : runMixed (words foreign) before = some foreignAfter)
    (run : runMixed (words script) before = some first)
    (movedRun : runMixed (words script) reordered = some second) :
    ∃ originalReplies reorderedReplies,
      NativePath program actor script before first originalReplies ∧
      NativePath program actor script reordered second reorderedReplies ∧
      RepliesRelated observe originalReplies reorderedReplies := by
  induction script generalizing before foreignAfter reordered row foreignRow with
  | nil =>
    change some before = some first at run
    change some reordered = some second at movedRun
    cases Option.some.inj run
    cases Option.some.inj movedRun
    exact ⟨[], [], .nil _, .nil _, .nil⟩
  | cons head tail ih =>
    change runMixed (head.word ++ words tail) before = some first at run
    change runMixed (head.word ++ words tail) reordered = some second at movedRun
    rw [split_word] at run movedRun
    obtain ⟨middle, firstHead, firstTail⟩ := Option.bind_eq_some_iff.mp run
    obtain ⟨movedMiddle, movedHead, movedTail⟩ := Option.bind_eq_some_iff.mp movedRun
    have headAllowed (edit) (member : edit ∈ ordinaryPart head.word) := allowed edit (by
      change edit ∈ ordinaryPart (head.word ++ words tail)
      simpa only [ordinaryPart, List.filterMap_append] using List.mem_append_left _ member)
    have tailAllowed (edit) (member : edit ∈ ordinaryPart (words tail)) := allowed edit (by
      change edit ∈ ordinaryPart (head.word ++ words tail)
      simpa only [ordinaryPart, List.filterMap_append] using List.mem_append_right _ member)
    have headBirths (control) (member : control ∈ controlPart head.word) := births control (by
      change control ∈ controlPart (head.word ++ words tail)
      simpa only [controlPart, List.filterMap_append] using List.mem_append_left _ member)
    have tailBirths (control) (member : control ∈ controlPart (words tail)) := births control (by
      change control ∈ controlPart (head.word ++ words tail)
      simpa only [controlPart, List.filterMap_append] using List.mem_append_right _ member)
    have pairedHead := mixed_respects ops observe laws head.word headAllowed paired
    rw [movedHead] at pairedHead
    cases foreignHead : runMixed head.word foreignAfter with
    | none => simp [foreignHead, OptionRel] at pairedHead
    | some foreignMiddle =>
      rw [foreignHead] at pairedHead
      have swapped := recorded_mixed_words_commute ops observe laws different separate
        (by rw [found]; exact Option.noConfusion) (by rw [foreignFound]; exact Option.noConfusion)
        headAllowed foreignAllowed firstHead foreignRun headBirths self.2
      rw [split_word, split_word, firstHead, foreignRun] at swapped
      change OptionRel _ (runMixed head.word foreignAfter) (runMixed (words foreign) middle) at swapped
      rw [foreignHead] at swapped
      cases foreignRunFromCut : runMixed (words foreign) middle with
      | none => simp [foreignRunFromCut, OptionRel] at swapped
      | some nextForeign =>
        rw [foreignRunFromCut] at swapped
        have relation : StampedRelated ops observe nextForeign movedMiddle :=
          ⟨swapped.1.symm.trans pairedHead.1, swapped.2.symm.trans pairedHead.2⟩
        have cutSelf := mixed_respects ops observe laws head.word headAllowed self
        rw [firstHead] at cutSelf
        obtain ⟨nextRow, nextFound, nextPayload, _⟩ := runMixed_keeps_row firstHead found
        obtain ⟨nextForeignRow, nextForeignFound, nextForeignPayload, _⟩ := runMixed_keeps_row firstHead foreignFound
        obtain ⟨reply, native⟩ := head.reify (ready head List.mem_cons_self) firstHead
        obtain ⟨otherReply, otherNative⟩ := head.reify (movedReady head List.mem_cons_self) movedHead
        have foreignNative := native_word_of_run foreign foreignFound foreignPayload foreignReady foreignOrigins foreignRun
        have comparison := head.pair_yields_after_foreign observe laws respect different found
          (by simpa only [payload] using separate) foreignNative paired (by
            intro child childPayload stamp member name entry vacant present
            obtain ⟨parent, otherStamp, fromForeign⟩ := runMixed_birth_of_new_row foreignRun vacant present
            have compatible := headBirths _ member _ fromForeign
            exact compatible.1) native otherNative
        obtain ⟨replies, otherReplies, later, movedLater, laterCompared⟩ := ih
          nextFound (nextPayload.trans payload) nextForeignFound (nextForeignPayload.trans foreignPayload) tailAllowed
          (fun letter member => letter.ready_after_word (ready letter (List.mem_cons_of_mem _ member)) firstHead)
          (fun letter member => letter.ready_after_word (movedReady letter (List.mem_cons_of_mem _ member)) movedHead)
          (fun letter member => letter.ready_after_word (foreignReady letter member) firstHead)
          tailBirths cutSelf relation foreignRunFromCut firstTail movedTail
        exact ⟨reply :: replies, otherReply :: otherReplies, .cons native later,
          .cons otherNative movedLater, .cons comparison laterCompared⟩

/-- Decode a recorded capture at its actual earlier trace position. The
original stamp belongs to that event, including when its raw name is reused. -/
theorem saved_from_trace {last time : Nat} (trace : GuardedHistory.Trace (encodeProgram program) last)
    (bounded : time ≤ last)
    {current : R} (currentEncoded : encodeRegistry ops current = trace.state time)
    {currentRow : Fiber Name V Code} (found : current actor = some currentRow)
    (capture : IncarnationReplay.Capture Name Key (Scalar ops))
    (recorded : capture ∈ (trace.notes time).2 actor) :
    ∃ saved : Saved program actor, saved.stamp = capture.index ∧ saved.stamp ≤ time ∧
      encodeInverse ops saved.token = capture.token ∧ (Letter.replay saved).origin_has currentRow.component ∧
      ∃ step < last, saved.stamp = step + 1 ∧ encodeRegistry ops saved.origin = trace.state step := by
  have rawFound : trace.state time actor = some (encodeFiber ops currentRow) := by
    simp [← currentEncoded, encodeRegistry, found]
  obtain ⟨age, step, earlier, stamp, sourceActor, rawRow, rawSource, payload, output, instruction, next, landed⟩ :=
    trace.capture_origin_component bounded rawFound capture recorded
  obtain ⟨source, encoded⟩ := GuardedTypedCuts.typed_cut trace step (Nat.le_of_lt earlier)
  rw [← encoded] at landed rawSource
  obtain ⟨sourceRow, sourceFound, sourceEncoded⟩ := encodeRegistry_some ops rawSource
  have component : sourceRow.component = currentRow.component :=
    (congrArg Calculus.Fiber.component sourceEncoded).trans payload
  obtain ⟨result, token, actual, _, captured⟩ := land_decode ops landed
  exact ⟨⟨source, result, instruction, token, next, capture.index, actual⟩,
    rfl, age, captured, ⟨sourceRow, sourceFound, component⟩, step, earlier, stamp, encoded⟩

private theorem birth_parent (script : List (Letter program actor)) {parent child : Name}
    {payload : Calculus.Component Key Code} {stamp : Nat}
    (member : Control.birth parent child payload stamp ∈ controlPart (words script)) : parent = actor := by
  obtain ⟨edit, belongs, selected⟩ := List.mem_filterMap.mp member
  obtain ⟨letter, _, inLetter⟩ := List.mem_flatMap.mp belongs
  cases letter with
  | replay saved =>
    cases token : saved.token <;> simp_all [Letter.word, Saved.word]
  | advance headCode head =>
    cases head <;> simp_all [Letter.word, Forward.word]

/-- Move one selected native landing across a recorded mixed word. The
foreign word remains executable from the original landing's output.
Its new endpoint relates to the moved landing's output at the next cut. -/
theorem landing_after_word (observe : ∀ key, Setoid (V key))
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, PaperObservationEquations.OperationRespects ops key (observe key).r)
    {foreignActor : Name} {component foreignComponent : Calculus.Component Key Code}
    {row foreignRow : Fiber Name V Code} {before foreignAfter alternate : SR}
    {middle : R} {token : I} {next : Option Code}
    (different : actor ≠ foreignActor) (separate : Transposition.Separated component foreignComponent)
    (found : before.1 actor = some row) (payload : row.component = component)
    (foreignFound : before.1 foreignActor = some foreignRow) (foreignPayload : foreignRow.component = foreignComponent)
    (landed : Land program actor code before.1 middle token next)
    (foreign : List (Letter program foreignActor))
    (foreignRun : runMixed (words foreign) before = some foreignAfter)
    (foreignReady : ∀ letter ∈ foreign, letter.ready before.1)
    (foreignOrigins : ∀ letter ∈ foreign, letter.origin_has foreignComponent)
    (initial : StampedRelated ops observe before before)
    (related : StampedRelated ops observe foreignAfter alternate)
    (stamp : Nat)
    (later : ∀ child earlier, Control.retire child earlier ∈ controlPart (words foreign) → earlier < stamp)
    (reservations : ∀ child declared, token = .retire child → (program code).action = .instantiate declared →
      ∀ parent other otherPayload otherStamp, Control.birth parent other otherPayload otherStamp ∈ controlPart (words foreign) →
        PairwiseAllocation.DrawCompatible child other declared otherPayload) :
    ∃ localCut foreignCut movedCut movedToken,
      localCut.1 = middle ∧
      Land program actor code alternate.1 movedCut.1 movedToken next ∧
      PairwiseForward.CaptureRelated observe token movedToken ∧
      replyAt program actor (capturedChild token) code before.1 =
        replyAt program actor (capturedChild movedToken) code alternate.1 ∧
      runMixed (words foreign) localCut = some foreignCut ∧
      StampedRelated ops observe localCut localCut ∧ StampedRelated ops observe foreignCut movedCut ∧
      ∀ letter ∈ foreign, letter.ready localCut.1 := by
  obtain ⟨head, ready, draw, localRun, stamped⟩ := Forward.record landed stamp
  have native := native_word_of_run foreign foreignFound foreignPayload foreignReady foreignOrigins foreignRun
  obtain ⟨moved, saved, rerun, capture, reply⟩ :=
    rerun_after_native_word observe laws found different (by simpa only [payload] using separate)
      landed native (by
        intro child declared retired action other entry vacant present
        obtain ⟨parent, otherStamp, inWord⟩ := runMixed_birth_of_new_row foreignRun vacant present
        exact reservations child declared retired action parent other entry.component otherStamp inWord)
  have foreignReadyHead := head.ready_after_word ready foreignRun
  have savedDraw := (transport_keeps_draw capture).trans draw
  have movedRun : runMixed head.word foreignAfter = some (moved, head.stamps foreignAfter.2) :=
    head.run_of_landing rerun foreignReadyHead savedDraw rfl
  have allowed : ∀ edit ∈ ordinaryPart head.word, Admitted ops actor component edit :=
    (Letter.advance code head).admitted found payload ready (by trivial)
  have foreignAllowed := script_admitted foreign foreignFound foreignPayload foreignReady foreignOrigins
  have checks : ∀ edit ∈ controlPart head.word, ∀ other ∈ controlPart (words foreign), Compatible edit other := by
    intro edit inHead other inForeign
    cases head with
    | unit action | provide key value action | operate owner key name argument action =>
      simp [Forward.word, controlPart] at inHead
    | birth child declared localStamp action =>
      have same : edit = Control.birth actor child declared localStamp := by
        simpa [Forward.word, controlPart] using inHead
      subst edit
      have sameStamp := stamped child declared localStamp inHead
      have chosen : token = .retire child := by
        cases token <;> simp_all [capturedChild, Forward.draw]
      cases other with
      | retire captured earlier =>
        exact .inr (by rw [sameStamp]; exact Nat.ne_of_gt (later captured earlier inForeign))
      | birth parent other otherPayload otherStamp =>
        have parentEq := birth_parent foreign inForeign
        subst parent
        have localVacant := birth_vacant_at_source _ localRun actor child declared localStamp inHead
        have foreignVacant := birth_vacant_at_source _ foreignRun foreignActor other otherPayload otherStamp inForeign
        exact ⟨reservations child declared chosen action _ _ _ _ inForeign,
          fun equal => Option.noConfusion (found.symm.trans (equal ▸ foreignVacant)),
          fun equal => Option.noConfusion (foreignFound.symm.trans (equal ▸ localVacant))⟩
  have localPresent : before.1 actor ≠ none := by rw [found]; exact Option.noConfusion
  have foreignPresent : before.1 foreignActor ≠ none := by rw [foreignFound]; exact Option.noConfusion
  have square := recorded_mixed_words_commute ops observe laws different separate
    localPresent foreignPresent allowed foreignAllowed localRun foreignRun checks initial.2
  rw [split_word, split_word, foreignRun, localRun] at square
  change OptionRel _ (runMixed head.word foreignAfter)
    (runMixed (words foreign) (middle, head.stamps before.2)) at square
  rw [movedRun] at square
  cases pushed : runMixed (words foreign) (middle, head.stamps before.2) with
  | none => simp [pushed, OptionRel] at square
  | some foreignCut =>
    rw [pushed] at square
    obtain ⟨movedOutput, movedToken, movedLand, pairedTable, pairedCapture, pairedReply⟩ :=
      PairwisePrograms.transport_landing observe program respect related.2 rerun
    have aligned : StampedRelated ops observe (moved, head.stamps foreignAfter.2)
        (movedOutput, head.stamps alternate.2) :=
      ⟨congrArg head.stamps related.1, pairedTable⟩
    have cutSelf := mixed_respects ops observe laws head.word allowed initial
    rw [localRun] at cutSelf
    exact ⟨(middle, head.stamps before.2), foreignCut, (movedOutput, head.stamps alternate.2), movedToken,
      rfl, movedLand, capture.symm.trans pairedCapture, reply.trans pairedReply, pushed,
      cutSelf, ⟨square.1.symm.trans aligned.1, square.2.symm.trans aligned.2⟩,
      fun letter member => letter.ready_after_word (foreignReady letter member) localRun⟩

/-- Cross-control compatibility follows from actual child reservations
and the origin of each saved retirement. An earlier capture cannot match
a later birth stamp. A capture from the same word uses that word's own
child draw, so the same cross-birth reservation check applies. -/
theorem control_compatibility_at_cut {leftActor rightActor : Name} {before leftAfter rightAfter : SR}
    (leftScript : List (Letter program leftActor)) (rightScript : List (Letter program rightActor))
    (leftPresent : before.1 leftActor ≠ none) (rightPresent : before.1 rightActor ≠ none)
    (leftRun : runMixed (words leftScript) before = some leftAfter)
    (rightRun : runMixed (words rightScript) before = some rightAfter) (time : Nat)
    (leftLater : ∀ child payload stamp, Control.birth leftActor child payload stamp ∈ controlPart (words leftScript) → time < stamp)
    (rightLater : ∀ child payload stamp, Control.birth rightActor child payload stamp ∈ controlPart (words rightScript) → time < stamp)
    (leftCaptures : ∀ child stamp, Control.retire child stamp ∈ controlPart (words leftScript) →
      stamp ≤ time ∨ ∃ payload, Control.birth leftActor child payload stamp ∈ controlPart (words leftScript))
    (rightCaptures : ∀ child stamp, Control.retire child stamp ∈ controlPart (words rightScript) →
      stamp ≤ time ∨ ∃ payload, Control.birth rightActor child payload stamp ∈ controlPart (words rightScript))
    (reservations : ∀ left payload i, Control.birth leftActor left payload i ∈ controlPart (words leftScript) →
      ∀ right other j, Control.birth rightActor right other j ∈ controlPart (words rightScript) →
      PairwiseAllocation.DrawCompatible left right payload other) :
    ∀ edit ∈ controlPart (words leftScript), ∀ other ∈ controlPart (words rightScript), Compatible edit other := by
  intro edit inLeft other inRight
  cases edit with
  | birth parent child payload stamp =>
    cases birth_parent leftScript inLeft
    cases other with
    | birth otherParent otherChild otherPayload otherStamp =>
      cases birth_parent rightScript inRight
      have leftVacant := birth_vacant_at_source _ leftRun leftActor child payload stamp inLeft
      have rightVacant := birth_vacant_at_source _ rightRun rightActor otherChild otherPayload otherStamp inRight
      exact ⟨reservations _ _ _ inLeft _ _ _ inRight,
        (fun same => leftPresent (same.symm ▸ rightVacant)),
        (fun same => rightPresent (same.symm ▸ leftVacant))⟩
    | retire otherChild otherStamp =>
      rcases rightCaptures _ _ inRight with old | ⟨otherPayload, captured⟩
      · exact .inr (Nat.ne_of_lt (Nat.lt_of_le_of_lt old (leftLater _ _ _ inLeft))).symm
      · exact .inl (reservations _ _ _ inLeft _ _ _ captured).1
  | retire child stamp =>
    cases other with
    | retire => exact True.intro
    | birth otherParent otherChild otherPayload otherStamp =>
      cases birth_parent rightScript inRight
      rcases leftCaptures _ _ inLeft with old | ⟨payload, captured⟩
      · exact .inr (Nat.ne_of_lt (Nat.lt_of_le_of_lt old (rightLater _ _ _ inRight))).symm
      · exact .inl (reservations _ _ _ captured _ _ _ inRight).1.symm

/-- Reflect both orders of a successful compatible mixed-word composition.
Each order preserves all selected continuations and relates the actual
typed partial captures. The comparison checks strict native inverse
domains at the reordered intermediate cuts. -/
theorem native_mixed_orders (observe : ∀ key, Setoid (V key))
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops
      (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, PaperObservationEquations.OperationRespects ops key (observe key).r)
    {leftActor rightActor : Name} {leftComponent rightComponent : Calculus.Component Key Code}
    (different : leftActor ≠ rightActor) (separate : Transposition.Separated leftComponent rightComponent)
    {leftScript : List (Letter program leftActor)} {rightScript : List (Letter program rightActor)}
    {before leftAfter rightAfter endpoint : SR}
    {leftRow rightRow : Fiber Name V Code}
    (leftFound : before.1 leftActor = some leftRow) (leftPayload : leftRow.component = leftComponent)
    (rightFound : before.1 rightActor = some rightRow) (rightPayload : rightRow.component = rightComponent)
    (leftReady : ∀ letter ∈ leftScript, Letter.ready letter before.1)
    (rightReady : ∀ letter ∈ rightScript, Letter.ready letter before.1)
    (leftOrigins : ∀ letter ∈ leftScript, Letter.origin_has letter leftComponent)
    (rightOrigins : ∀ letter ∈ rightScript, Letter.origin_has letter rightComponent)
    (leftRun : runMixed (words leftScript) before = some leftAfter)
    (rightRun : runMixed (words rightScript) before = some rightAfter)
    (births : ∀ edit ∈ controlPart (words leftScript),
      ∀ other ∈ controlPart (words rightScript), Compatible edit other)
    (source : StampedRelated ops observe before before)
    (ordered : runMixed (words leftScript ++ words rightScript) before = some endpoint) :
    ∃ reversed leftReplies rightReplies reversedRightReplies reversedLeftReplies,
      NativePath program leftActor leftScript before leftAfter leftReplies ∧
      NativePath program rightActor rightScript leftAfter endpoint rightReplies ∧
      NativePath program rightActor rightScript before rightAfter reversedRightReplies ∧
      NativePath program leftActor leftScript rightAfter reversed reversedLeftReplies ∧
      RepliesRelated observe leftReplies reversedLeftReplies ∧
      RepliesRelated observe reversedRightReplies rightReplies ∧
      StampedRelated ops observe reversed endpoint := by
  have leftAllowed := script_admitted leftScript leftFound leftPayload leftReady leftOrigins
  have rightAllowed := script_admitted rightScript rightFound rightPayload rightReady rightOrigins
  have leftPresent : before.1 leftActor ≠ none := by rw [leftFound]; exact Option.noConfusion
  have rightPresent : before.1 rightActor ≠ none := by rw [rightFound]; exact Option.noConfusion
  have commute := recorded_mixed_words_commute_related ops observe laws different separate leftPresent rightPresent
    leftAllowed rightAllowed leftRun rightRun births source
  rw [ordered, split_word, rightRun] at commute
  change OptionRel _ (runMixed (words leftScript) rightAfter) (some endpoint) at commute
  cases reversedRun : runMixed (words leftScript) rightAfter with
  | none => simp [reversedRun, OptionRel] at commute
  | some reversed =>
    have related : StampedRelated ops observe reversed endpoint := by simpa [reversedRun, OptionRel] using commute
    have orderedTail : runMixed (words rightScript) leftAfter = some endpoint := by
      simpa [split_word, leftRun] using ordered
    have leftSelf := mixed_respects ops observe laws (words leftScript) leftAllowed source
    have rightSelf := mixed_respects ops observe laws (words rightScript) rightAllowed source
    rw [leftRun] at leftSelf
    rw [rightRun] at rightSelf
    obtain ⟨leftReplies, reversedLeftReplies, leftNative, reversedLeftNative, leftCompared⟩ :=
      pair_script_after_foreign observe laws respect different separate leftScript rightScript
        leftFound leftPayload rightFound rightPayload leftAllowed rightAllowed leftReady
        (fun letter member => letter.ready_after_word (leftReady letter member) rightRun)
        rightReady rightOrigins births source rightSelf rightRun leftRun reversedRun
    obtain ⟨reversedRightReplies, rightReplies, reversedRightNative, rightNative, rightCompared⟩ :=
      pair_script_after_foreign observe laws respect (Ne.symm different) separate.symm rightScript leftScript
        rightFound rightPayload leftFound leftPayload rightAllowed leftAllowed rightReady
        (fun letter member => letter.ready_after_word (rightReady letter member) leftRun)
        leftReady leftOrigins (fun other otherMem edit editMem => (births edit editMem other otherMem).symm)
        source leftSelf leftRun rightRun orderedTail
    exact ⟨reversed, leftReplies, rightReplies, reversedRightReplies, reversedLeftReplies,
      leftNative, rightNative, reversedRightNative, reversedLeftNative, leftCompared, rightCompared, related⟩

/-- Native execution version of the mixed generator square. The inputs
carry their actual results, routes and capture origins. The alternate
order reproduces the selected continuations and compares the captures
against these exact original executions. -/
theorem native_paths_commute (observe : ∀ key, Setoid (V key))
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, PaperObservationEquations.OperationRespects ops key (observe key).r)
    {leftActor rightActor : Name} {leftRow rightRow : Fiber Name V Code}
    (different : leftActor ≠ rightActor) (separate : Transposition.Separated leftRow.component rightRow.component)
    {leftScript : List (Letter program leftActor)} {rightScript : List (Letter program rightActor)}
    {before leftAfter rightAfter endpoint : SR} {leftReplies rightReplies laterReplies : List ReplyT}
    (leftFound : before.1 leftActor = some leftRow) (rightFound : before.1 rightActor = some rightRow)
    (leftOrigins : ∀ letter ∈ leftScript, Letter.origin_has letter leftRow.component)
    (rightOrigins : ∀ letter ∈ rightScript, Letter.origin_has letter rightRow.component)
    (left : NativePath program leftActor leftScript before leftAfter leftReplies)
    (right : NativePath program rightActor rightScript before rightAfter rightReplies)
    (ordered : NativePath program rightActor rightScript leftAfter endpoint laterReplies)
    (births : ∀ edit ∈ controlPart (words leftScript),
      ∀ other ∈ controlPart (words rightScript), Compatible edit other)
    (source : StampedRelated ops observe before before) :
    ∃ reversed reversedReplies, NativePath program leftActor leftScript rightAfter reversed reversedReplies ∧
      RepliesRelated observe leftReplies reversedReplies ∧ RepliesRelated observe rightReplies laterReplies ∧
      StampedRelated ops observe reversed endpoint := by
  have composed : runMixed (words leftScript ++ words rightScript) before = some endpoint := by
    simpa [split_word, left.record] using ordered.record
  obtain ⟨reversed, firstReplies, afterLeft, firstRight, reversedReplies, firstNative, afterLeftNative, firstRightNative,
    reversedNative, leftCompared, rightCompared, endpoints⟩ := native_mixed_orders observe laws respect different separate
      leftFound rfl rightFound rfl (left.ready leftFound) (right.ready rightFound) leftOrigins rightOrigins left.record right.record
      births source composed
  rw [firstNative.replies_eq left] at leftCompared
  rw [firstRightNative.replies_eq right, afterLeftNative.replies_eq ordered] at rightCompared
  exact ⟨reversed, reversedReplies, reversedNative, leftCompared, rightCompared, endpoints⟩

/-- The same native square also compares failure. Under the guarded
partial interpretation neither order can succeed unless the other does. -/
theorem native_paths_same_domain (observe : ∀ key, Setoid (V key))
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    {leftActor rightActor : Name} {leftRow rightRow : Fiber Name V Code}
    (different : leftActor ≠ rightActor) (separate : Transposition.Separated leftRow.component rightRow.component)
    {leftScript : List (Letter program leftActor)} {rightScript : List (Letter program rightActor)}
    {before leftAfter rightAfter : SR} {leftReplies rightReplies : List ReplyT}
    (leftFound : before.1 leftActor = some leftRow) (rightFound : before.1 rightActor = some rightRow)
    (leftOrigins : ∀ letter ∈ leftScript, Letter.origin_has letter leftRow.component)
    (rightOrigins : ∀ letter ∈ rightScript, Letter.origin_has letter rightRow.component)
    (left : NativePath program leftActor leftScript before leftAfter leftReplies)
    (right : NativePath program rightActor rightScript before rightAfter rightReplies)
    (births : ∀ edit ∈ controlPart (words leftScript),
      ∀ other ∈ controlPart (words rightScript), Compatible edit other)
    (source : PairwisePrograms.Related (ops := ops) observe before.1 before.1) :
    (∃ endpoint replies, NativePath program rightActor rightScript leftAfter endpoint replies) ↔
      (∃ endpoint replies, NativePath program leftActor leftScript rightAfter endpoint replies) := by
  have leftPresent : before.1 leftActor ≠ none := by rw [leftFound]; exact Option.noConfusion
  have rightPresent : before.1 rightActor ≠ none := by rw [rightFound]; exact Option.noConfusion
  have leftAllowed := script_admitted leftScript leftFound rfl (left.ready leftFound) leftOrigins
  have rightAllowed := script_admitted rightScript rightFound rfl (right.ready rightFound) rightOrigins
  have commute := recorded_mixed_words_commute ops observe laws different separate leftPresent rightPresent
    leftAllowed rightAllowed left.record right.record births source
  rw [split_word, split_word, left.record, right.record] at commute
  change OptionRel _ (runMixed (words leftScript) rightAfter) (runMixed (words rightScript) leftAfter) at commute
  constructor
  · rintro ⟨endpoint, replies, ordered⟩
    rw [ordered.record] at commute
    cases reversed : runMixed (words leftScript) rightAfter with
    | none => simp [reversed, OptionRel] at commute
    | some moved =>
      obtain ⟨selected, actual⟩ := reify_path leftScript
        (fun letter member => letter.ready_after_word (left.ready leftFound letter member) right.record) reversed
      exact ⟨moved, selected, actual⟩
  · rintro ⟨endpoint, replies, reversed⟩
    rw [reversed.record] at commute
    cases ordered : runMixed (words rightScript) leftAfter with
    | none => simp [ordered, OptionRel] at commute
    | some moved =>
      obtain ⟨selected, actual⟩ := reify_path rightScript
        (fun letter member => letter.ready_after_word (right.ready rightFound letter member) left.record) ordered
      exact ⟨moved, selected, actual⟩

end Cordis.Repairs.PairwiseNativeWords
