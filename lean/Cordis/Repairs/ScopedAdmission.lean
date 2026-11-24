import Cordis.Repairs.ScopedProgram

/-! Synthesize the continuation entry links of a scoped iterator from
its primitive domains and actual outcome selection. -/
namespace Cordis.Repairs.ScopedAdmission
open TypedRegistry ScopedEffects ScopedProgram
open PaperEffectEquations (CoeffectOperations)
open Iterators (OptionRel)
universe u
variable {Name Key Code : Type u} {V : Key → Type u}
variable [DecidableEq Name] [DecidableEq Key] {ops : CoeffectOperations V}
local notation "R" => Registry Name V Code
local notation "Dom" => R → Prop
variable {program : Code → Instruction Name ops Code} {actor : Name}
variable {observe : ∀ key, Setoid (V key)} {keys : Key → Prop}
variable {code : Code} {source target : Registry Name V Code → Prop} {O : Type u}

inductive Unlinked (program : Code → Instruction Name ops Code) (actor : Name)
    (observe : ∀ key, Setoid (V key)) (keys : Key → Prop) : Code → Type (u + 1)
  | stage {code : Code} {source target : Dom} {O : Type u}
      (head : Head program actor observe keys code source target O)
      (tail : ∀ reply next, (program code).next (head.reply reply) = some next →
        Unlinked program actor observe keys next) : Unlinked program actor observe keys code

local notation "Recipe" => Unlinked program actor observe keys

def Unlinked.draw (recipe : Recipe code) : Option Name :=
  match recipe with
  | .stage head _ => head.draw

structure Admitted (program : Code → Instruction Name ops Code) (actor : Name)
    (observe : ∀ key, Setoid (V key)) (keys : Key → Prop) (code : Code) where
  domain : Dom
  iterator : ScopedProgram.Iterator program actor observe keys code domain

local notation "Plan" => Admitted program actor observe keys

private def entryDomain (head : Head program actor observe keys code source target O)
    (tails : ∀ reply next, (program code).next (head.reply reply) = some next → Plan next) : Dom :=
  fun state => source state ∧
    ∀ (primitive : source state) output saved reply next
      (selected : (program code).next (head.reply reply) = some next),
      head.effect.run ⟨state, primitive⟩ = some (output, saved, reply) →
      (tails reply next selected).domain output.val

/-- The synthesized input domain consists of states admitted by the head
whose successful selected continuation also admits the head's result. -/
def compile : {code : Code} → Recipe code → Plan code
  | _, .stage head tail =>
    let tails := fun reply next selected => compile (tail reply next selected)
    { domain := entryDomain head tails
      iterator :=
        .stage (head.narrow (fun _ admitted => admitted.1))
          (fun reply state => ∀ next selected, (tails reply next selected).domain state)
          (fun reply next selected =>
            (tails reply next selected).iterator.narrow (fun _ admitted => admitted next selected))
          (by
            intro input output saved reply next called selected next' selected'
            exact input.property.2 input.property.1 output saved reply next' selected' called) }

/-- Once a primitive succeeds and selects a continuation, admission of
the compiled source is exactly admission of that continuation at its output. -/
theorem compile_stage_domain_of_call
    {head : Head program actor observe keys code source target O}
    {tail : ∀ reply next, (program code).next (head.reply reply) = some next → Recipe next}
    (input : State source) {output : State target} {saved : Saved target} {reply : O} {next : Code}
    (called : head.effect.run input = some (output, saved, reply))
    (selected : (program code).next (head.reply reply) = some next) :
    (compile (.stage head tail)).domain input.val ↔ (compile (tail reply next selected)).domain output.val := by
  constructor
  · intro admitted
    exact admitted.2 input.property output saved reply next selected called
  · intro admitted
    refine ⟨input.property, ?_⟩
    intro proof otherOutput otherSaved otherReply following followingSelected otherCalled
    change head.effect.run input = _ at otherCalled
    cases Option.some.inj (called.symm.trans otherCalled)
    cases Option.some.inj (selected.symm.trans followingSelected)
    exact admitted

-- A successful or failed primitive call is recorded independently of the
-- synthesized domain. A successful continuation has its own legal call.
inductive Runs (program : Code → Instruction Name ops Code) (actor : Name)
    (observe : ∀ key, Setoid (V key)) (keys : Key → Prop) :
    {code : Code} → Unlinked program actor observe keys code → R → Option R → Prop
  | failed {code source target O} {state : R}
      {head : Head program actor observe keys code source target O}
      {tail : ∀ reply next, (program code).next (head.reply reply) = some next →
        Unlinked program actor observe keys next}
      (input : source state) (called : head.effect.run ⟨state, input⟩ = none) :
      Runs program actor observe keys (.stage head tail) state none
  | last {code source target O} {state : R}
      {head : Head program actor observe keys code source target O}
      {tail : ∀ reply next, (program code).next (head.reply reply) = some next →
        Unlinked program actor observe keys next}
      (input : source state) (output : State target) (saved : Saved target) (reply : O)
      (called : head.effect.run ⟨state, input⟩ = some (output, saved, reply))
      (selected : (program code).next (head.reply reply) = none) :
      Runs program actor observe keys (.stage head tail) state (some output.val)
  | next {code source target O} {state : R}
      {head : Head program actor observe keys code source target O}
      {tail : ∀ reply next, (program code).next (head.reply reply) = some next →
        Unlinked program actor observe keys next}
      (input : source state) (output : State target) (saved : Saved target) (reply : O)
      (called : head.effect.run ⟨state, input⟩ = some (output, saved, reply))
      (following : Code) (selected : (program code).next (head.reply reply) = some following)
      {result : Option R} (continued : Runs program actor observe keys (tail reply following selected) output.val result) :
      Runs program actor observe keys (.stage head tail) state result

theorem admits_run {recipe : Recipe code} {state : R} {result : Option R}
    (run : Runs program actor observe keys recipe state result) : (compile recipe).domain state := by
  induction run with
  | failed input called =>
    refine ⟨input, ?_⟩
    intro _ output saved reply next selected impossible
    rw [called] at impossible
    cases impossible
  | last input output saved reply called terminal =>
    refine ⟨input, ?_⟩
    intro _ output' saved' reply' next selected other
    cases Option.some.inj (called.symm.trans other)
    rw [terminal] at selected
    cases selected
  | next input output saved reply called following selected continued ih =>
    refine ⟨input, ?_⟩
    intro _ output' saved' reply' next selected' other
    cases Option.some.inj (called.symm.trans other)
    have codeEq := Option.some.inj (selected.symm.trans selected')
    subst next
    exact ih

theorem run_of_admitted (recipe : Recipe code) (input : State (compile recipe).domain) :
    Runs program actor observe keys recipe input.val ((compile recipe).iterator.execute input) := by
  induction recipe with
  | stage head tail ih =>
    simp only [compile, ScopedProgram.Iterator.execute, Head.narrow]
    split
    next missed => exact .failed _ missed
    next output saved reply called =>
      split
      next terminal => exact .last _ output saved reply called terminal
      next next selected =>
        simp only [ScopedProgram.Iterator.execute_narrow]
        have ready := input.property.2 input.property.1 output saved reply next selected called
        exact .next _ output saved reply called next selected (ih reply next selected ⟨output.val, ready⟩)

theorem Runs.unique {recipe : Recipe code} {state : R} {result : Option R}
    (first : Runs program actor observe keys recipe state result) {other : Option R}
    (second : Runs program actor observe keys recipe state other) : result = other := by
  induction first generalizing other with
  | failed input called =>
    cases second with
    | failed => rfl
    | last input' _ _ _ called' _ =>
      rw [called] at called'
      cases called'
    | next input' _ _ _ called' _ _ _ =>
      rw [called] at called'
      cases called'
  | last input output saved reply called terminal =>
    cases second with
    | failed input' called' =>
      rw [called] at called'
      cases called'
    | last input' output' _ _ called' _ =>
      rw [called] at called'
      cases Option.some.inj called'
      rfl
    | next input' _ _ _ called' _ selected _ =>
      rw [called] at called'
      cases Option.some.inj called'
      rw [terminal] at selected
      cases selected
  | next input output saved reply called following selected continued ih =>
    cases second with
    | failed input' called' =>
      rw [called] at called'
      cases called'
    | last input' _ _ _ called' terminal =>
      rw [called] at called'
      cases Option.some.inj called'
      rw [terminal] at selected
      cases selected
    | next input' _ _ _ called' following' selected' tail' =>
      rw [called] at called'
      cases Option.some.inj called'
      have codeEq := Option.some.inj (selected.symm.trans selected')
      subst following'
      exact ih tail'

/-- The compiled domain accepts exactly the complete computations through
the native primitive scopes, including a genuine primitive failure. -/
theorem runs_iff {recipe : Recipe code} {state : R} {result : Option R} :
    Runs program actor observe keys recipe state result ↔
      ∃ input : (compile recipe).domain state, (compile recipe).iterator.execute ⟨state, input⟩ = result := by
  constructor
  · intro run
    refine ⟨admits_run run, ?_⟩
    exact (run_of_admitted recipe _).unique run
  · rintro ⟨input, rfl⟩
    exact run_of_admitted recipe ⟨state, input⟩

end Cordis.Repairs.ScopedAdmission
