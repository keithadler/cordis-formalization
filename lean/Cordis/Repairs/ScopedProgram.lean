import Cordis.Repairs.ScopedRollbackDomains

/-!
A finite mediated iterator with a domain for each head. The native outcome
selects the tail. Entry to that tail is justified at each successful landing;
it is not an additional fallible operation on related inputs. Both probes use
the same instance of each primitive, including its chosen name at a birth.
-/
namespace Cordis.Repairs.ScopedProgram
open TypedRegistry ScopedEffects
open PaperEffectEquations (CoeffectOperations)
open Iterators (OptionRel)
universe u
variable {Name Key Code : Type u} {V : Key → Type u}
variable [DecidableEq Name] [DecidableEq Key] {ops : CoeffectOperations V}
local notation "R" => Registry Name V Code
local notation "Dom" => R → Prop

variable (program : Code → Instruction Name ops Code) (actor : Name)
variable (observe : ∀ key, Setoid (V key)) (keys : Key → Prop)

structure Head (code : Code) (source target : Dom) (O : Type u) where
  effect : Effect source target O
  reply : O → Outcome Name ops
  reply_injective : Function.Injective reply
  draw : Option Name
  lawful : Lawful observe keys effect
  realizes : Realizes program actor code reply effect draw
  /-- A continuing head keeps its inverse domain available during the tail. -/
  outputStable : ∀ outcome next, (program code).next (reply outcome) = some next →
    ScopedRollback.Stable ops target

variable {program actor observe keys}
variable {source target : Registry Name V Code → Prop} {O : Type u} {code : Code}

namespace Head

/-- Carry extra facts on the input domain. The original forward is used
verbatim on admitted inputs; inverse probes retain the original domain. -/
def narrow {smaller : Dom} (head : Head program actor observe keys code source target O)
    (included : ∀ state, smaller state → source state) :
    Head program actor observe keys code smaller target O where
  effect := ⟨fun input => head.effect.run ⟨input.val, included input.val input.property⟩⟩
  reply := head.reply
  reply_injective := head.reply_injective
  draw := head.draw
  lawful :=
    ⟨fun _ _ _ _ called => head.lawful.recover _ _ _ _ called,
      fun _ _ related => head.lawful.respect _ _ related⟩
  realizes :=
    ⟨fun _ _ _ _ called => head.realizes.sound _ _ _ _ called,
      by
        intro input _ _ _ landed drawn
        exact head.realizes.complete ⟨input.val, included input.val input.property⟩ landed drawn⟩
  outputStable := head.outputStable

def unit (action : (program code).action = .unit)
    (terminal : (program code).next .unit = none) (source : Dom) :
    Head program actor observe keys code source source PUnit.{u+1} where
  effect := ScopedEffects.unit source
  reply _ := .unit
  reply_injective := by intro first second _; cases first; cases second; rfl
  draw := none
  lawful := unit_lawful observe keys source
  realizes := unit_realizes program actor code action source
  outputStable := by
    intro _ _ continues
    rw [terminal] at continues
    cases continues

def provision {acting : Calculus.Component Key Code} (key : Key) (selected : keys key)
    (provided : acting.provides key = true) (value : V key)
    (action : (program code).action = .provide key value) :
    Head program actor observe keys code (CompatibleProvision.Compatible ops actor acting)
      (CompatibleProvision.Compatible ops actor acting) PUnit.{u+1} where
  effect := ScopedEffects.provision key provided value
  reply _ := .provision key value
  reply_injective := by intro first second _; cases first; cases second; rfl
  draw := none
  lawful := provision_lawful observe keys key selected provided value
  realizes := provision_realizes program code key provided value action
  outputStable _ _ _ := ScopedRollback.Stable.provision _ _ _

def operate {owner : Name} {acting providing : Calculus.Component Key Code} {key : Key}
    (selected : keys key) (provided : providing.provides key = true)
    (name : ops.Name key) (argument : ops.Argument key name)
    (witness : PartialInverseObservation.Witnessed (ops.operation key name argument) (observe key).r)
    (action : (program code).action = .operate key name argument) :
    Head program actor observe keys code
      (BoundOperation.Compatible ops actor acting owner providing key)
      (BoundOperation.Compatible ops actor acting owner providing key) (ops.Outcome key name) where
  effect := ScopedEffects.operate provided name argument
  reply := .operation key name
  reply_injective := by
    intro first second same
    injection same
  draw := none
  lawful := operate_lawful observe keys selected provided name argument witness
  realizes := operate_realizes program code provided name argument action
  outputStable _ _ _ := ScopedRollback.Stable.operate _ _ _ _ _ _

def allocate (newborn : Name) {acting child : Calculus.Component Key Code}
    (action : (program code).action = .instantiate child) :
    Head program actor observe keys code
      (fun state : R => CompatibleProvision.Compatible ops actor acting state ∧
        Insertable state newborn child (some actor))
      (fun state : R => CompatibleProvision.Compatible ops actor acting state ∧
        ∃ fiber, state newborn = some fiber ∧ fiber.component = child ∧ fiber.parent = some actor)
      PUnit.{u+1} where
  effect := ScopedEffects.allocate
  reply _ := .child newborn
  reply_injective := by intro first second _; cases first; cases second; rfl
  draw := some newborn
  lawful := allocate_lawful observe keys
  realizes := allocate_realizes program code action
  outputStable _ _ _ := ScopedRollback.Stable.allocate _ _ _ _ _

end Head

/-- A stage's continuation is indexed by the *native* selected code, and the
link discharges entry to its domain for every successful forward probe. -/
inductive Iterator (program : Code → Instruction Name ops Code) (actor : Name)
    (observe : ∀ key, Setoid (V key)) (keys : Key → Prop) : Code → Dom → Type (u + 1)
  | stage {code : Code} {source target : Dom} {O : Type u}
      (head : Head program actor observe keys code source target O)
      (entry : O → Dom)
      (tail : ∀ outcome next, (program code).next (head.reply outcome) = some next →
        Iterator program actor observe keys next (entry outcome))
      (link : ∀ input output saved outcome next, head.effect.run input = some (output, saved, outcome) →
        (program code).next (head.reply outcome) = some next → entry outcome output.val) :
      Iterator program actor observe keys code source

/-- The paper's actual successive landings for the selected codes. This
models one calculation by the iterator, before per-rule lifecycle bookkeeping.
It retains the list of captured native tokens, in forward order. -/
inductive Landings (program : Code → Instruction Name ops Code) (actor : Name) :
    Code → R → R → List (Inverse Name V) → Prop
  | last {code before after token} : Land program actor code before after token none →
      Landings program actor code before after [token]
  | next {code following before middle after token tokens} :
      Land program actor code before middle token (some following) →
      Landings program actor following middle after tokens →
      Landings program actor code before after (token :: tokens)

namespace Iterator

/-- Definition 56's unit is a terminal iterator. -/
def terminalUnit (action : (program code).action = .unit)
    (terminal : (program code).next .unit = none) :
    Iterator program actor observe keys code source :=
  .stage (Head.unit action terminal source) (fun _ => source)
    (by intro _ _ continues; rw [Head.unit, terminal] at continues; cases continues)
    (by intro _ output _ _ _ _ _; exact output.property)

/-- Refine the initial probe domain while retaining the native head and
all its continuation and rollback domains. -/
def narrow {smaller : Dom} (it : Iterator program actor observe keys code source)
    (included : ∀ state, smaller state → source state) :
    Iterator program actor observe keys code smaller :=
  match it with
  | .stage head entry tail link =>
    .stage (head.narrow included) entry tail
      (fun input output saved outcome next called selected =>
        link ⟨input.val, included input.val input.property⟩ output saved outcome next called selected)

@[simp] theorem narrow_self (it : Iterator program actor observe keys code source)
    (included : ∀ state, source state → source state) : it.narrow included = it := by
  cases it with
  | stage head entry tail link =>
    cases head
    rfl

def execute : {code : Code} → {source : Dom} →
    Iterator program actor observe keys code source → State source → Option R
  | code, _, .stage head _ tail link, input =>
    match called : head.effect.run input with
    | none => none
    | some (output, saved, outcome) =>
      match selected : (program code).next (head.reply outcome) with
      | none => some output.val
      | some next => (tail outcome next selected).execute ⟨output.val, link input output saved outcome next called selected⟩

@[simp] theorem execute_narrow {smaller : Dom} (it : Iterator program actor observe keys code source)
    (included : ∀ state, smaller state → source state) (input : State smaller) :
    (it.narrow included).execute input = it.execute ⟨input.val, included input.val input.property⟩ := by
  cases it
  simp only [narrow, execute, Head.narrow]

/-- Every successful evaluation is a native sequence, with its actual
outcomes, chosen continuation codes and saved inverse tokens. -/
theorem execute_sound (it : Iterator program actor observe keys code source) (input : State source)
    (output : R) (called : it.execute input = some output) :
    ∃ tokens, Landings program actor code input.val output tokens := by
  induction it with
  | stage head entry tail link ih =>
    simp only [execute] at called
    split at called
    · cases called
    next result r h =>
      obtain ⟨token, landing, _⟩ := head.realizes.sound _ _ _ _ h
      split at called
      next hNext =>
        rw [hNext] at landing
        cases called
        exact ⟨_, .last landing⟩
      next next hNext =>
        rw [hNext] at landing
        obtain ⟨tokens, rest⟩ := ih _ _ hNext _ called
        exact ⟨_, .next landing rest⟩

/-- A continuation can change domains and keys. Related probes agree about
whether the whole sequence returns and about the final observable table.
The scalar witness and the explicit entry proof are used at every head. -/
theorem execute_respects (it : Iterator program actor observe keys code source)
    (left right : State source) (related : Observed observe keys left right) :
    OptionRel (TypedStateObservation.TablesRelatedAt observe keys) (it.execute left) (it.execute right) := by
  induction it with
  | stage head entry tail link ih =>
    have compared := head.lawful.respect left right related
    simp only [execute]
    split
    next h =>
      split
      · trivial
      next b bi y rCalled =>
        rw [h, rCalled] at compared
        exact False.elim compared
    next a ai x lCalled =>
      split
      next atEnd =>
        split
        next absent =>
          rw [lCalled, absent] at compared
          exact False.elim compared
        next b bi y rCalled =>
          rw [lCalled, rCalled] at compared
          obtain ⟨outputs, _, outcomes⟩ := compared
          change x = y at outcomes
          subst y
          split
          · exact outputs
          next next impossible =>
            rw [atEnd] at impossible
            cases impossible
      next next chosen =>
        split
        next absent =>
          rw [lCalled, absent] at compared
          exact False.elim compared
        next b bi y rCalled =>
          rw [lCalled, rCalled] at compared
          obtain ⟨outputs, _, outcomes⟩ := compared
          change x = y at outcomes
          subst y
          split
          next impossible =>
            rw [chosen] at impossible
            cases impossible
          next next' chosen' =>
            have equal : next = next' := Option.some.inj (chosen.symm.trans chosen')
            subst next'
            exact ih x next chosen _ _ outputs

end Iterator

end Cordis.Repairs.ScopedProgram
