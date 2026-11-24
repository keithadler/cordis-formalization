import Cordis.Repairs.MediatedRoutes

/-! Definition 34 for the admitted native iterator grammar. Each head
has its own input domain and each yielded inverse has its own probe
domain. The continuation relation follows the native selected branches. -/
namespace Cordis.Repairs.ScopedIteratorObservation
open TypedRegistry ScopedEffects ScopedProgram
open PaperEffectEquations (CoeffectOperations)
open Iterators (OptionRel)

universe u
variable {Name Key Code : Type u} {V : Key → Type u}
variable [DecidableEq Name] [DecidableEq Key] {ops : CoeffectOperations V}
local notation "R" => Registry Name V Code
local notation "Dom" => R → Prop
local notation "Program" => Code → Instruction Name ops Code
structure Node (program : Code → Instruction Name ops Code) (actor : Name)
    (observe : ∀ key, Setoid (V key)) (keys : Key → Prop) where
  code : Code
  domain : Dom
  iterator : ScopedProgram.Iterator program actor observe keys code domain

structure Yield (program : Code → Instruction Name ops Code) (actor : Name)
    (observe : ∀ key, Setoid (V key)) (keys : Key → Prop) where
  domain : Dom
  output : State domain
  inverse : Saved domain
  reply : Outcome Name ops
  next : Option (Node program actor observe keys)
  admits_next : ∀ node, next = some node → node.domain output.val

variable {program : Code → Instruction Name ops Code} {actor : Name}
variable {observe : ∀ key, Setoid (V key)} {keys : Key → Prop}
local notation "N" => Node program actor observe keys
local notation "Y" => Yield program actor observe keys

def Node.compiled {code : Code} (recipe : ScopedAdmission.Unlinked program actor observe keys code) : N :=
  let admitted := ScopedAdmission.compile recipe
  ⟨code, admitted.domain, admitted.iterator⟩

private theorem narrow_node_eq {code : Code} {domain narrower : R → Prop}
    (iterator : ScopedProgram.Iterator program actor observe keys code domain)
    (included : ∀ state, narrower state → domain state) (equal : narrower = domain) :
    (⟨code, narrower, iterator.narrow included⟩ : N) = ⟨code, domain, iterator⟩ := by
  subst narrower
  rw [ScopedProgram.Iterator.narrow_self]

def Node.evaluate (node : N) (input : State node.domain) : Option Y :=
  match node with
  | ⟨code, _, .stage head entry tail link⟩ =>
    match called : head.effect.run input with
    | none => none
    | some (output, inverse, reply) =>
      match selected : (program code).next (head.reply reply) with
      | none => some ⟨_, output, inverse, head.reply reply, none, by intro _ impossible; cases impossible⟩
      | some following =>
        some ⟨_, output, inverse, head.reply reply, some ⟨following, entry reply, tail reply following selected⟩, by
          intro node paired
          cases Option.some.inj paired
          exact link input output inverse reply following called selected⟩

/-- A selected continuation of a compiled stage is the compilation of
the actual selected recipe. The proof-indexed domain in the compiler
expresses that single continuation's domain. -/
theorem compiled_next {code : Code} {source target : R → Prop} {O : Type u}
    {head : Head program actor observe keys code source target O}
    {tail : ∀ reply next, (program code).next (head.reply reply) = some next →
      ScopedAdmission.Unlinked program actor observe keys next}
    (input : State (Node.compiled (.stage head tail)).domain)
    {result : Y} {following : N}
    (called : (Node.compiled (.stage head tail)).evaluate input = some result)
    (continued : result.next = some following) :
    ∃ (reply : O) (next : Code) (selected : (program code).next (head.reply reply) = some next),
      result.reply = head.reply reply ∧ following = Node.compiled (tail reply next selected) := by
  simp only [Node.compiled, ScopedAdmission.compile, Node.evaluate, Head.narrow] at called
  split at called
  · contradiction
  next output inverse reply success =>
    split at called
    · cases Option.some.inj called
      cases continued
    next next selected =>
      cases Option.some.inj called
      cases Option.some.inj continued
      refine ⟨reply, next, selected, rfl, ?_⟩
      apply narrow_node_eq
      funext state
      apply propext
      refine ⟨fun admitted => admitted next selected, ?_⟩
      intro admitted other found
      cases Option.some.inj (selected.symm.trans found)
      exact admitted

/-- The inverse returned by a compiled call retains its primitive
output domain. -/
theorem compiled_yield_domain {code : Code} {source target : R → Prop} {O : Type u}
    {head : Head program actor observe keys code source target O}
    {tail : ∀ reply next, (program code).next (head.reply reply) = some next →
      ScopedAdmission.Unlinked program actor observe keys next}
    (input : State (Node.compiled (.stage head tail)).domain) {result : Y}
    (called : (Node.compiled (.stage head tail)).evaluate input = some result) :
    result.domain = target := by
  simp only [Node.compiled, ScopedAdmission.compile, Node.evaluate, Head.narrow] at called
  split at called
  · contradiction
  next output inverse reply success =>
    split at called <;> cases Option.some.inj called <;> rfl

/-- A generated forward head is reached through actual successful yields
and their selected continuations. Each witness uses its own admitted probe. -/
inductive Reach (root : N) : N → Prop where
  | root : Reach root root
  | next {current following : N} (prior : Reach root current)
      (input : State current.domain) (result : Y)
      (called : current.evaluate input = some result) (selected : result.next = some following) :
      Reach root following

section Mediated
open MediatedAdmission
variable {component : Calculus.Component Key Code}
local notation "MN" => Node program actor observe (Interface component)
local notation "MY" => Yield program actor observe (Interface component)

/-- A probe admitted by the compiled native grammar contains the acting
component. The primitive scope supplies this fact before every call. -/
theorem mediated_scope (choices : Choices ops Name Code) (lawful : OperationsLawful ops observe)
    {code : Code} (grammar : Mediated program component code) (history : List (Outcome Name ops))
    {state : R} (admitted : (Node.compiled (recipe (actor := actor) choices lawful grammar history)).domain state) :
    CompatibleProvision.Compatible ops actor component state := by
  obtain ⟨source, target, O, head, shape, frame, _, _⟩ := recipe_stage (actor := actor) choices lawful grammar history
  rw [shape] at admitted
  exact frame state admitted.1

private theorem mediated_next (choices : Choices ops Name Code) (lawful : OperationsLawful ops observe)
    {code : Code} (grammar : Mediated program component code) (history : List (Outcome Name ops))
    (input : State (Node.compiled (recipe (actor := actor) choices lawful grammar history)).domain)
    {result : MY} {following : MN}
    (called : (Node.compiled (recipe (actor := actor) choices lawful grammar history)).evaluate input = some result)
    (continued : result.next = some following) :
    ∃ (next : Code) (selected : (program code).next result.reply = some next),
      following = Node.compiled
        (recipe choices lawful (successor grammar ⟨result.reply, selected⟩) (result.reply :: history)) := by
  obtain ⟨source, target, O, head, shape, _, _, _⟩ := recipe_stage (actor := actor) choices lawful grammar history
  revert called input
  rw [shape]
  intro input called
  obtain ⟨reply, next, selected, observed, reached⟩ := compiled_next input called continued
  have picked : (program code).next result.reply = some next := by rw [observed]; exact selected
  refine ⟨next, picked, ?_⟩
  rw [reached]
  congr
  exact observed.symm

/-- Reachability through the actual yields of an admitted native iterator
keeps the original route and draw functions and appends the typed outcome
of each selected stage to the history. -/
theorem Reach.mediated (choices : Choices ops Name Code) (lawful : OperationsLawful ops observe)
    {code : Code} (grammar : Mediated program component code) (history : List (Outcome Name ops)) {node : MN}
    (reached : Reach (Node.compiled (recipe choices lawful grammar history)) node) :
    ∃ (current : Code) (remaining : Mediated program component current) (past : List (Outcome Name ops)),
      node = Node.compiled (recipe choices lawful remaining past) := by
  induction reached with
  | root => exact ⟨code, grammar, history, rfl⟩
  | next _ input result called selected ih =>
    obtain ⟨current, remaining, past, rfl⟩ := ih
    obtain ⟨next, picked, following⟩ := mediated_next choices lawful remaining past input called selected
    exact ⟨next, successor remaining ⟨result.reply, picked⟩, result.reply :: past, following⟩

/-- The saved inverse's own probe domain survives any native word that
keeps the declared component, provider route, and allocated child row. -/
theorem mediated_inverse_frame (choices : Choices ops Name Code) (lawful : OperationsLawful ops observe)
    {code : Code} (grammar : Mediated program component code) (history : List (Outcome Name ops))
    (input : State (Node.compiled (recipe (actor := actor) choices lawful grammar history)).domain)
    {result : MY}
    (called : (Node.compiled (recipe (actor := actor) choices lawful grammar history)).evaluate input = some result)
    {before after : R} (kept : ScopedRollback.Keeps ops before after) :
    result.domain before → result.domain after := by
  obtain ⟨source, target, O, head, shape, _, preserves, _⟩ := recipe_stage (actor := actor) choices lawful grammar history
  revert called input
  rw [shape]
  intro input called
  rw [compiled_yield_domain input called]
  exact preserves kept

/-- Two calls to the same compiled head retain its primitive output
domain. The actual capturing landing identifies the observed slot. -/
theorem mediated_inverse_scope (choices : Choices ops Name Code) (lawful : OperationsLawful ops observe)
    {code : Code} (grammar : Mediated program component code) (history : List (Outcome Name ops))
    {first second output : R} {token : Inverse Name V} {next : Option Code}
    (a : (Node.compiled (recipe (actor := actor) choices lawful grammar history)).domain first)
    (b : (Node.compiled (recipe (actor := actor) choices lawful grammar history)).domain second)
    {left right : MY}
    (called : (Node.compiled (recipe (actor := actor) choices lawful grammar history)).evaluate ⟨first, a⟩ = some left)
    (other : (Node.compiled (recipe (actor := actor) choices lawful grammar history)).evaluate ⟨second, b⟩ = some right)
    (landed : Land program actor code first output token next) :
    left.domain = right.domain ∧ InverseScope ops (Interface component) token left.domain := by
  obtain ⟨source, target, O, head, shape, _, _, captures⟩ :=
    recipe_stage (actor := actor) choices lawful grammar history
  revert called other a b
  rw [shape]
  intro a b called other
  rw [compiled_yield_domain ⟨first, a⟩ called, compiled_yield_domain ⟨second, b⟩ other]
  exact ⟨rfl, captures a.1 landed⟩

end Mediated

def Yield.finish (yielded : Y) : Option R :=
  match selected : yielded.next with
  | none => some yielded.output.val
  | some node => node.iterator.execute ⟨yielded.output.val, yielded.admits_next node selected⟩

theorem Yield.finish_end (yielded : Y) (terminal : yielded.next = none) :
    yielded.finish = some yielded.output.val := by
  unfold Yield.finish
  split
  · rfl
  next _ selected => cases terminal.symm.trans selected

theorem Yield.finish_next (yielded : Y) {node : N} (selected : yielded.next = some node) :
    yielded.finish = node.iterator.execute ⟨yielded.output.val, yielded.admits_next node selected⟩ := by
  unfold Yield.finish
  split
  next terminal => cases terminal.symm.trans selected
  next actual found =>
    cases Option.some.inj (found.symm.trans selected)
    rfl

theorem Node.execute_eq (node : N) (input : State node.domain) :
    node.iterator.execute input = (node.evaluate input).bind Yield.finish := by
  obtain ⟨code, source, stage⟩ := node
  cases stage with
  | stage head entry tail link =>
    simp only [Node.evaluate, ScopedProgram.Iterator.execute]
    split
    next absent =>
      split
      · rfl
      next _ _ _ called => cases absent.symm.trans called
    next output saved reply called =>
      split
      next terminal =>
        split
        next absent => cases absent.symm.trans called
        next output' saved' reply' called' =>
          cases Option.some.inj (called.symm.trans called')
          split
          · rfl
          next _ selected => cases terminal.symm.trans selected
      next following selected =>
        split
        next absent => cases absent.symm.trans called
        next output' saved' reply' called' =>
          cases Option.some.inj (called.symm.trans called')
          split
          next terminal => cases terminal.symm.trans selected
          next _ selected' =>
            cases Option.some.inj (selected.symm.trans selected')
            rfl

/-- Every successful observation is the actual native head. Its selected
code and its inverse agree with the native landing on their scopes. -/
def Node.draw (node : N) : Option Name :=
  match node.iterator with
  | .stage head .. => head.draw

theorem compiled_draw {code : Code} (recipe : ScopedAdmission.Unlinked program actor observe keys code) :
    (Node.compiled recipe).draw = recipe.draw := by
  cases recipe
  rfl

theorem chosen_landing_draw (choices : MediatedAdmission.Choices ops Name Code)
    (lawful : MediatedAdmission.OperationsLawful ops observe)
    {component : Calculus.Component Key Code} {code : Code} (grammar : MediatedAdmission.Mediated program component code)
    (history : List (Outcome Name ops)) {before after : R} {token : Inverse Name V} {next : Option Code}
    (landed : Land program actor code before after token next)
    (matched : MediatedAdmission.Matches choices history code before token) :
    capturedChild token = (Node.compiled (MediatedAdmission.recipe (actor := actor) choices lawful grammar history)).draw := by
  rw [compiled_draw, MediatedAdmission.recipe_draw]
  cases landed with
  | unit _ _ _ action | provide _ _ _ _ _ _ action _ _ _
      | operate _ _ _ _ _ _ _ _ _ _ _ action _ _ => simp [action, capturedChild]
  | instantiate _ _ _ _ child action _ =>
    change choices.draw code history = child at matched
    simp [action, capturedChild, matched]

theorem Node.evaluate_native (node : N) (input : State node.domain) (result : Y)
    (called : node.evaluate input = some result) :
    ∃ token, Land program actor node.code input.val result.output.val token (result.next.map Node.code) ∧
      InverseAgrees result.inverse token ∧ capturedChild token = node.draw ∧
      replyAt program actor node.draw node.code input.val = some result.reply := by
  obtain ⟨code, source, stage⟩ := node
  cases stage with
  | stage head entry tail link =>
    simp only [Node.evaluate] at called
    split at called
    · contradiction
    next output inverse reply success =>
      obtain ⟨token, landed, saved, drawn, exactReply⟩ := head.realizes.sound _ _ _ _ success
      split at called
      · rename_i terminal
        cases Option.some.inj called
        exact ⟨token, by simpa only [terminal] using landed, saved, drawn, exactReply⟩
      · rename_i following selected
        cases Option.some.inj called
        exact ⟨token, by simpa only [selected] using landed, saved, drawn, exactReply⟩

/-- Equal typed outcomes select the very same continuation of one scoped
node, including its domain and all later outcome-dependent draws. -/
theorem Node.next_eq_of_reply (node : N) (first second : State node.domain) (a b : Y)
    (left : node.evaluate first = some a) (right : node.evaluate second = some b)
    (reply : a.reply = b.reply) : a.next = b.next := by
  obtain ⟨code, source, stage⟩ := node
  cases stage with
  | stage head entry tail link =>
    simp only [Node.evaluate] at left right
    split at left
    · contradiction
    next output saved result called =>
      split at right
      · contradiction
      next other otherSaved otherResult otherCalled =>
        split at left <;> split at right <;>
          cases Option.some.inj left <;> cases Option.some.inj right
        · rfl
        · rename_i terminal next selected
          change head.reply result = head.reply otherResult at reply
          rw [← reply, terminal] at selected
          cases selected
        · rename_i next selected terminal
          change head.reply result = head.reply otherResult at reply
          rw [reply, terminal] at selected
          cases selected
        · rename_i next selected otherNext otherSelected
          have same := head.reply_injective reply
          subst otherResult
          cases Option.some.inj (selected.symm.trans otherSelected)
          rfl

/-- A native landing on an admitted probe with the head's own draw gives
a successful scoped yield. No successful call from outside the scope is used. -/
theorem Node.evaluate_of_native (node : N) (input : State node.domain)
    {after : R} {token : Inverse Name V} {next : Option Code}
    (landed : Land program actor node.code input.val after token next)
    (drawn : capturedChild token = node.draw) : ∃ result, node.evaluate input = some result := by
  obtain ⟨code, source, stage⟩ := node
  cases stage with
  | stage head entry tail link =>
    obtain ⟨⟨output, inverse, reply⟩, called⟩ := head.realizes.complete input landed drawn
    simp only [Node.evaluate]
    split
    next absent => rw [called] at absent; cases absent
    next =>
      split <;> exact ⟨_, rfl⟩

/-- The relation of successful heads compares the state, the entire
partial inverse function on compatible probes, and the selected tails. -/
def YieldRelated (relation : N → N → Prop) (left right : Y) : Prop :=
  Observed observe keys left.output right.output ∧
    (∀ first second, Observed observe keys first second →
      OptionRel (Observed observe keys) (left.inverse first) (right.inverse second)) ∧
    OptionRel relation left.next right.next

def Unfold (relation : N → N → Prop) (left right : N) : Prop :=
  ∀ first second, Observed observe keys first second →
    OptionRel (YieldRelated relation) (left.evaluate first) (right.evaluate second)

def Related (left right : N) : Prop :=
  ∃ relation : N → N → Prop, relation left right ∧ ∀ a b, relation a b → Unfold relation a b

theorem related_unfold {left right : N} (related : Related left right) : Unfold Related left right := by
  obtain ⟨relation, pair, closed⟩ := related
  intro first second observed
  apply OptionRel.mono (fun a b output => ?_) (closed left right pair first second observed)
  exact ⟨output.1, output.2.1, OptionRel.mono (fun _ _ tails => ⟨relation, tails, closed⟩) output.2.2⟩

private theorem evaluate_self (node : N) : Unfold Eq node node := by
  obtain ⟨code, source, stage⟩ := node
  cases stage with
  | stage head entry tail link =>
    intro first second observed
    have replies := head.lawful.respect first second observed
    simp only [Node.evaluate]
    split
    next leftMissing =>
      split
      · trivial
      next data rightCalled =>
        rw [leftMissing, rightCalled] at replies
        exact False.elim replies
    next a ai outcome leftCalled =>
      split
      next leftLast =>
        split
        next rightMissing =>
          rw [leftCalled, rightMissing] at replies
          exact False.elim replies
        next b bi otherOutcome rightCalled =>
          rw [leftCalled, rightCalled] at replies
          obtain ⟨state, inverses, same⟩ := replies
          change outcome = otherOutcome at same
          subst otherOutcome
          split
          · exact ⟨state, inverses, trivial⟩
          next code impossible => rw [leftLast] at impossible; cases impossible
      next following leftNext =>
        split
        next rightMissing =>
          rw [leftCalled, rightMissing] at replies
          exact False.elim replies
        next b bi otherOutcome rightCalled =>
          rw [leftCalled, rightCalled] at replies
          obtain ⟨state, inverses, same⟩ := replies
          change outcome = otherOutcome at same
          subst otherOutcome
          split
          next impossible => rw [leftNext] at impossible; cases impossible
          next nextCode rightNext =>
            have fixed := Option.some.inj (leftNext.symm.trans rightNext)
            subst nextCode
            exact ⟨state, inverses, rfl⟩

/-- The whole admitted iterator is witnessed by the recursive function
relation. The proof uses each selected head's local laws on its own scope. -/
theorem self_related (node : N) : Related node node :=
  ⟨Eq, rfl, fun a _ equal => equal ▸ evaluate_self a⟩

/-- The recursive relation compares the complete native calculations as
well as their individual yields. Each selected continuation takes its
input through the domain link carried by that yield. -/
theorem execute_related {code : Code} {source : Dom}
    (left : ScopedProgram.Iterator program actor observe keys code source) (right : N)
    (first : State source) (second : State right.domain)
    (pair : Related ⟨code, source, left⟩ right) (observed : Observed observe keys first second) :
    OptionRel (TypedStateObservation.TablesRelatedAt observe keys) (left.execute first) (right.iterator.execute second) := by
  induction left generalizing right with
  | @stage code source target O head entry tail link ih =>
    let node : N := ⟨code, source, .stage head entry tail link⟩
    change Related node right at pair
    change OptionRel _ (node.iterator.execute first) _
    rw [node.execute_eq, right.execute_eq]
    have corresponding := related_unfold pair first second observed
    cases moved : right.evaluate second with
    | none =>
      rw [moved] at corresponding
      cases called : node.evaluate first <;> simp only [called, OptionRel, Option.bind_none] at corresponding ⊢
    | some other =>
      rw [moved] at corresponding
      simp only [Node.evaluate, node] at corresponding ⊢
      split at corresponding
      · exact False.elim corresponding
      next output inverse reply called =>
        split at corresponding
        next terminal =>
          obtain ⟨tables, _, tails⟩ := corresponding
          cases continuation : other.next with
          | none =>
            simp only [Option.bind_some, other.finish_end continuation]
            exact tables
          | some found => simp [continuation, OptionRel] at tails
        next following selected =>
          obtain ⟨tables, _, tails⟩ := corresponding
          cases continuation : other.next with
          | none => simp [continuation, OptionRel] at tails
          | some found =>
            have nextPair : Related ⟨following, entry reply, tail reply following selected⟩ found := by
              simpa only [continuation, OptionRel] using tails
            have compared := ih reply following selected found
              ⟨output.val, link first output inverse reply following called selected⟩
              ⟨other.output.val, other.admits_next found continuation⟩ nextPair tables
            simp only [Option.bind_some, other.finish_next continuation]
            exact compared

/-- All provider choices and all outcome-dependent fresh draws admitted
by the native finite grammar satisfy the recursive relation. -/
theorem mediated_related (actor : Name) {component : Calculus.Component Key Code} {code : Code}
    (choices : MediatedAdmission.Choices ops Name Code) (lawful : MediatedAdmission.OperationsLawful ops observe)
    (grammar : MediatedAdmission.Mediated program component code) (history : List (Outcome Name ops)) :
    let admitted := MediatedAdmission.admit (actor := actor) choices lawful grammar history
    let node : Node program actor observe (MediatedAdmission.Interface component) := ⟨code, admitted.domain, admitted.iterator⟩
    Related node node := by
  dsimp only
  exact self_related _

end Cordis.Repairs.ScopedIteratorObservation
