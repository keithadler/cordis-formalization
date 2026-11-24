import Cordis.Repairs.ScopedConfinement

/-! The native mediated grammar supplies every branch of a scoped recipe.
A route fixes the provider's interface. Fresh draws may depend on the
complete outcome prefix that led to the current code. -/
namespace Cordis.Repairs.MediatedAdmission
open TypedRegistry ScopedProgram ScopedAdmission ScopedEffects
open PaperEffectEquations (CoeffectOperations)
universe u
variable {Name Key Code : Type u} {V : Key → Type u}
variable [DecidableEq Name] [DecidableEq Key] {ops : CoeffectOperations V}
local notation "R" => Registry Name V Code
variable {program : Code → Instruction Name ops Code} {actor : Name}
variable {observe : ∀ key, Setoid (V key)}
variable {component : Calculus.Component Key Code} {code next : Code}

abbrev Required (component : Calculus.Component Key Code) (key : Key) := component.requires key = true
abbrev Provided (component : Calculus.Component Key Code) (key : Key) := component.provides key = true
abbrev Interface (component : Calculus.Component Key Code) (key : Key) :=
  Required component key ∨ Provided component key

abbrev Mediated (program : Code → Instruction Name ops Code) (component : Calculus.Component Key Code) :=
  MediatedRegistry.Mediated (encodeProgram program) (Required component) (Provided component)

def Selected (program : Code → Instruction Name ops Code) (following current : Code) : Prop :=
  ∃ reply, (program current).next reply = some following

omit [DecidableEq Name] in
private theorem selected_encoded {reply : Outcome Name ops}
    (selected : (program code).next reply = some next) :
    (encodeProgram program code).next (encodeOutcome ops reply) = some next :=
  (encodeInstruction_next (program code) reply).trans selected

omit [DecidableEq Name] in
theorem successor (mediated : Mediated program component code) (step : Selected program next code) :
    Mediated program component next := by
  obtain ⟨reply, selected⟩ := step
  cases mediated with
  | unit _ _ terminal =>
    have impossible := selected_encoded selected
    rw [terminal] at impossible
    cases impossible
  | operation _ _ _ _ _ tails => exact tails _ _ (selected_encoded selected)
  | provision _ _ _ _ _ tails => exact tails _ _ (selected_encoded selected)
  | birth _ _ _ tails => exact tails _ _ (selected_encoded selected)

omit [DecidableEq Name] in
theorem accessible (mediated : Mediated program component code) : Acc (Selected program) code := by
  induction mediated with
  | unit code action terminal =>
    refine Acc.intro code (fun following step => ?_)
    obtain ⟨reply, selected⟩ := step
    have impossible := selected_encoded selected
    rw [terminal] at impossible
    cases impossible
  | operation code _ _ _ _ _ ih | provision code _ _ _ _ _ ih | birth code _ _ _ ih =>
    exact Acc.intro code (fun following ⟨reply, selected⟩ => ih _ _ (selected_encoded selected))

def Declared (program : Code → Instruction Name ops Code)
    (component : Calculus.Component Key Code) (code : Code) : Prop :=
  match (program code).action with
  | .unit => (program code).next .unit = none
  | .provide key _ => Provided component key
  | .operate key _ _ => Interface component key
  | .instantiate _ => True

omit [DecidableEq Name] in
theorem declared (mediated : Mediated program component code) : Declared program component code := by
  cases mediated with
  | unit code action terminal =>
    unfold Declared
    cases actual : (program code).action <;> simp [encodeProgram, encodeInstruction, encodeAction, actual] at action
    exact (encodeInstruction_next (program code) .unit).symm.trans (terminal _)
  | operation code key run action allowed _ =>
    unfold Declared
    cases actual : (program code).action <;> simp [encodeProgram, encodeInstruction, encodeAction, actual] at action
    exact Eq.mpr (congrArg (Interface component) action.1) allowed
  | provision code key value action allowed _ =>
    unfold Declared
    cases actual : (program code).action <;> simp [encodeProgram, encodeInstruction, encodeAction, actual] at action
    exact Eq.mpr (congrArg (Provided component) action.1) allowed
  | birth code payload action _ =>
    unfold Declared
    cases actual : (program code).action <;> simp [encodeProgram, encodeInstruction, encodeAction, actual] at action
    trivial

structure Route (Name : Type u) (Code : Type u) (key : Key) where
  owner : Name
  provider : Calculus.Component Key Code
  provides : Provided provider key

structure Choices (ops : CoeffectOperations V) (Name Code : Type u) where
  route : ∀ key : Key, Option (Route Name Code key)
  draw : Code → List (Outcome Name ops) → Name

abbrev OperationsLawful (ops : CoeffectOperations V) (observe : ∀ key, Setoid (V key)) :=
  ∀ key name (argument : ops.Argument key name),
    PartialInverseObservation.Witnessed (ops.operation key name argument) (observe key).r

omit [DecidableEq Name] [DecidableEq Key] in
theorem lawful_of_contracts (ops : CoeffectOperations V) (observe : ∀ key, Setoid (V key))
    (recovery : PaperEffectEquations.ValueOperationWitness ops)
    (respect : ∀ key, PaperObservationEquations.OperationRespects ops key (observe key).r) : OperationsLawful ops observe := by
  intro key name argument
  exact ⟨fun input output inverse reply called =>
    ⟨input, recovery key name argument input output inverse reply called, (observe key).refl input⟩,
    fun left right related => respect key name argument left right related⟩

private def unavailableHead :
    Head program actor observe (Interface component) code (fun _ => False) (fun _ => False) PEmpty.{u + 1} :=
    { effect := ⟨fun input => False.elim input.property⟩
      reply := fun impossible => nomatch impossible
      reply_injective := fun impossible => nomatch impossible
      draw := none
      lawful := ⟨fun input => False.elim input.property, fun input => False.elim input.property⟩
      realizes := ⟨fun input => False.elim input.property, fun input => False.elim input.property⟩
      outputStable := fun impossible => nomatch impossible }

private def recipeStepAt (choices : Choices ops Name Code) (lawful : OperationsLawful ops observe)
    (grammar : Mediated program component code) (history : List (Outcome Name ops))
    (rest : ∀ reply next, (program code).next reply = some next →
      Unlinked program actor observe (Interface component) next)
    (primitive : Action Name ops Code) (isAction : (program code).action = primitive) :
    Unlinked program actor observe (Interface component) code :=
  match primitive, isAction with
  | .unit, action =>
    have terminal : (program code).next .unit = none := by simpa only [Declared, action] using declared grammar
    .stage (Head.unit action terminal (CompatibleProvision.Compatible ops actor component))
      (fun _ => rest .unit)
  | .provide key value, action =>
    have provided : Provided component key := by simpa only [Declared, action] using declared grammar
    .stage (Head.provision key (.inr provided) provided value action)
      (fun _ => rest (.provision key value))
  | .operate key name argument, action =>
    have allowed : Interface component key := by simpa only [Declared, action] using declared grammar
    match choices.route key with
    | none => .stage unavailableHead (fun impossible => nomatch impossible)
    | some route =>
      .stage (Head.operate (owner := route.owner) (acting := component)
        allowed route.provides name argument (lawful key name argument) action)
        (fun reply => rest (.operation key name reply))
  | .instantiate child, action =>
    let newborn := choices.draw code history
    .stage (Head.allocate (acting := component) newborn action)
      (fun _ => rest (.child newborn))


private def recipeStep (choices : Choices ops Name Code) (lawful : OperationsLawful ops observe)
    (grammar : Mediated program component code) (history : List (Outcome Name ops))
    (rest : ∀ reply next, (program code).next reply = some next →
      Unlinked program actor observe (Interface component) next) :
    Unlinked program actor observe (Interface component) code :=
  recipeStepAt choices lawful grammar history rest (program code).action rfl

private theorem recipeStep_eq (choices : Choices ops Name Code) (lawful : OperationsLawful ops observe)
    (grammar : Mediated program component code) (history : List (Outcome Name ops))
    (rest : ∀ reply next, (program code).next reply = some next →
      Unlinked program actor observe (Interface component) next)
    {primitive : Action Name ops Code} (action : (program code).action = primitive) :
    recipeStep choices lawful grammar history rest = recipeStepAt choices lawful grammar history rest primitive action := by
  cases action
  rfl

/-- Construct the recipe directly from the paper's finite continuation
grammar, using the given provider routes and fresh choices. The argument
to the draw function records the native outcomes, most recent first. -/
noncomputable def recipe (choices : Choices ops Name Code) (lawful : OperationsLawful ops observe)
    (mediated : Mediated program component code) (history : List (Outcome Name ops) := []) :
    Unlinked program actor observe (Interface component) code :=
  (accessible mediated).recOn
    (motive := fun current _ => Mediated program component current → List (Outcome Name ops) →
      Unlinked program actor observe (Interface component) current)
    (fun _ _ recurse grammar prior =>
      recipeStep choices lawful grammar prior (fun reply next selected =>
        recurse next ⟨reply, selected⟩ (successor grammar ⟨reply, selected⟩) (reply :: prior)))
    mediated history

theorem recipe_eq (choices : Choices ops Name Code) (lawful : OperationsLawful ops observe)
    (mediated : Mediated program component code) (history : List (Outcome Name ops)) :
    recipe (actor := actor) choices lawful mediated history =
      recipeStep choices lawful mediated history (fun reply _ selected =>
        recipe choices lawful (successor mediated ⟨reply, selected⟩) (reply :: history)) := by
  conv =>
    lhs
    unfold recipe
  generalize accessible mediated = acc
  cases acc
  rfl

/-- Inspect a canonical recipe's primitive domains and exact
outcome-indexed tail. The primitive output domain is preserved by native
mixed words even when the primitive is terminal. -/
theorem recipe_stage (choices : Choices ops Name Code) (lawful : OperationsLawful ops observe)
    (grammar : Mediated program component code) (history : List (Outcome Name ops)) :
    ∃ (source target : R → Prop) (O : Type u)
      (head : Head program actor observe (Interface component) code source target O),
      recipe choices lawful grammar history = .stage head
        (fun reply _ selected =>
          recipe choices lawful (successor grammar ⟨head.reply reply, selected⟩) (head.reply reply :: history)) ∧
      (∀ state, source state → CompatibleProvision.Compatible ops actor component state) ∧
      (∀ {before after}, ScopedRollback.Keeps ops before after → target before → target after) ∧
      (∀ {before after token next}, source before → Land program actor code before after token next →
        ScopedEffects.InverseScope ops (Interface component) token target) := by
  rw [recipe_eq]
  cases action : (program code).action with
  | unit =>
    rw [recipeStep_eq _ _ _ _ _ action]
    have terminal : (program code).next .unit = none := by simpa only [Declared, action] using declared grammar
    exact ⟨_, _, _, Head.unit action terminal (CompatibleProvision.Compatible ops actor component),
      rfl, fun _ inside => inside, fun kept old => kept.compatible old, by
        intro _ _ _ _ _ landed
        cases landed <;> simp_all [ScopedEffects.InverseScope]⟩
  | provide key value =>
    rw [recipeStep_eq _ _ _ _ _ action]
    have provides : Provided component key := by simpa only [Declared, action] using declared grammar
    exact ⟨_, _, _, Head.provision key (.inr provides) provides value action,
      rfl, fun _ inside => inside, fun kept old => kept.compatible old, by
        intro _ _ _ _ _ landed
        cases landed with
        | provide _ _ _ _ used given instructed _ _ _ =>
          cases action.symm.trans instructed
          exact ⟨.inr provides, component, provides, fun _ inside => inside⟩
        | unit _ _ _ instructed | operate _ _ _ _ _ _ _ _ _ _ _ instructed _ _
          | instantiate _ _ _ _ _ instructed _ => cases action.symm.trans instructed⟩
  | operate key name argument =>
    rw [recipeStep_eq _ _ _ _ _ action]
    have access : Interface component key := by simpa only [Declared, action] using declared grammar
    cases routed : choices.route key with
    | none =>
      simp only [recipeStepAt, routed]
      refine ⟨_, _, _, unavailableHead, ?_, fun _ impossible => False.elim impossible,
        fun _ impossible => impossible, by intro _ _ _ _ impossible; cases impossible⟩
      congr 1
      funext impossible
      cases impossible
    | some route =>
      simp only [recipeStepAt, routed]
      exact ⟨_, _, _, Head.operate (owner := route.owner) access route.provides name argument
        (lawful key name argument) action, rfl, fun _ inside => inside.1, fun kept old => kept.bound old, by
          intro before _ _ _ inside landed
          cases landed with
          | operate _ _ _ used op argument owner input output inverse reply instructed located _ =>
            cases action.symm.trans instructed
            have routed : bindingOwner before actor key = some owner := by
              unfold location at located
              obtain ⟨provider, found, paired⟩ := Option.bind_eq_some_iff.mp located
              obtain ⟨_, _, equal⟩ := Option.map_eq_some_iff.mp paired
              exact found.trans (congrArg (fun value => some value.1) equal)
            have sameOwner := Option.some.inj (routed.symm.trans inside.2.2)
            subst owner
            exact ⟨access, route.provider, route.provides, fun _ probe => probe.2.1⟩
          | unit _ _ _ instructed | provide _ _ _ _ _ _ instructed _ _ _
            | instantiate _ _ _ _ _ instructed _ => cases action.symm.trans instructed⟩
  | instantiate child =>
    rw [recipeStep_eq _ _ _ _ _ action]
    exact ⟨_, _, _, Head.allocate (acting := component) (choices.draw code history) action,
      rfl, fun _ inside => inside.1, fun kept old => kept.allocated old, by
        intro _ _ _ _ _ landed
        cases landed <;> simp_all [ScopedEffects.InverseScope]⟩

theorem recipe_draw (choices : Choices ops Name Code) (lawful : OperationsLawful ops observe)
    (grammar : Mediated program component code) (history : List (Outcome Name ops)) :
    (recipe (actor := actor) choices lawful grammar history).draw =
      match (program code).action with
      | .instantiate _ => some (choices.draw code history)
      | _ => none := by
  rw [recipe_eq]
  cases action : (program code).action with
  | operate key name argument =>
    rw [recipeStep_eq _ _ _ _ _ action]
    cases routed : choices.route key <;> simp [recipeStepAt, routed, ScopedAdmission.Unlinked.draw, unavailableHead, Head.operate]
  | unit | provide | instantiate => rw [recipeStep_eq _ _ _ _ _ action]; rfl

noncomputable def admit (choices : Choices ops Name Code) (lawful : OperationsLawful ops observe)
    (mediated : Mediated program component code) (history : List (Outcome Name ops) := []) :
    ScopedAdmission.Admitted program actor observe (Interface component) code :=
  compile (recipe choices lawful mediated history)

/-- The native reply used to extend the allocator's history. A successful
landing supplies the declaration and guard proofs separately. -/
abbrev nativeReply (program : Code → Instruction Name ops Code) (actor draw : Name)
    (code : Code) (state : R) : Option (Outcome Name ops) :=
  replyAt program actor (some draw) code state

def Matches (choices : Choices ops Name Code) (history : List (Outcome Name ops)) (code : Code)
    (before : R) : Inverse Name V → Prop
  | .retire child => choices.draw code history = child
  | .operate owner key _ =>
    ∃ route, choices.route key = some route ∧ owner = route.owner ∧
      ∃ provider, before owner = some provider ∧ provider.component = route.provider
  | .unit | .restrict _ _ => True

theorem chosen_reply_at {choices : Choices ops Name Code} {history : List (Outcome Name ops)}
    {before after : R} {token : Inverse Name V} {next : Option Code}
    (landed : Land program actor code before after token next)
    (matching : Matches choices history code before token) :
    replyAt program actor (capturedChild token) code before =
      nativeReply program actor (choices.draw code history) code before := by
  cases landed with
  | unit _ _ _ action | provide _ _ _ _ _ _ action _ _ _
    | operate _ _ _ _ _ _ _ _ _ _ _ action _ _ => simp [replyAt, action]
  | instantiate _ _ _ _ child action _ =>
    have same : choices.draw code history = child := matching
    simp [replyAt, capturedChild, action, same]

private theorem run_stage {source target : Registry Name V Code → Prop} {O : Type u}
    {head : Head program actor observe (Interface component) code source target O}
    {tail : ∀ reply next, (program code).next (head.reply reply) = some next →
      Unlinked program actor observe (Interface component) next}
    (input : State source) (output : State target) (saved : Saved target) (reply : O)
    (called : head.effect.run input = some (output, saved, reply)) (result : Option R)
    (terminal : (program code).next (head.reply reply) = none → result = some output.val)
    (continues : ∀ next (selected : (program code).next (head.reply reply) = some next),
      Runs program actor observe (Interface component) (tail reply next selected) output.val result) :
    Runs program actor observe (Interface component) (.stage head tail) input.val result := by
  cases selected : (program code).next (head.reply reply) with
  | none =>
    rw [terminal selected]
    exact .last input.property output saved reply called selected
  | some next => exact .next input.property output saved reply called next selected (continues next selected)

omit [DecidableEq Name] [DecidableEq Key] in
theorem bound_by_location {state : R} {actor owner : Name} {key : Key} {value : V key}
    (located : location state actor key = some (owner, value)) :
    bindingOwner state actor key = some owner ∧ tableAt state owner key = some value := by
  unfold location at located
  cases found : bindingOwner state actor key with
  | none => simp [found] at located
  | some selected =>
    cases binding : tableAt state selected key with
    | none => simp [found, binding] at located
    | some held =>
      have same : selected = owner ∧ held = value := by simpa [found, binding] using located
      obtain ⟨rfl, rfl⟩ := same
      exact ⟨rfl, binding⟩

private theorem reflect_landing (choices : Choices ops Name Code) (lawful : OperationsLawful ops observe)
    (grammar : Mediated program component code) (history : List (Outcome Name ops))
    {before after : R} {token : Inverse Name V} {next : Option Code}
    (landed : Land program actor code before after token next)
    (compatible : CompatibleProvision.Compatible ops actor component before)
    (matching : Matches choices history code before token)
    (result : Option R) (terminal : next = none → result = some after)
    (continues : ∀ reply following,
      nativeReply program actor (choices.draw code history) code before = some reply →
      (selected : (program code).next reply = some following) →
      next = some following →
      Runs program actor observe (Interface component)
        (recipe choices lawful (successor grammar ⟨reply, selected⟩) (reply :: history)) after result) :
    Runs program actor observe (Interface component) (recipe choices lawful grammar history) before result := by
  rw [recipe_eq]
  cases landed with
  | unit _ actor code action =>
    rw [recipeStep_eq _ _ _ _ _ action]
    simp only [recipeStepAt]
    have ready : (program code).next .unit = none := by
      simpa only [Declared, action] using declared grammar
    apply run_stage (program := program) (actor := actor) (observe := observe) (component := component) ⟨before, compatible⟩ ⟨before, compatible⟩ some PUnit.unit rfl result terminal
    intro next selected
    change (program code).next .unit = some next at selected
    rw [ready] at selected
    cases selected
  | provide _ actor code row key value action present declared absent =>
    rw [recipeStep_eq _ _ _ _ _ action]
    simp only [recipeStepAt]
    obtain ⟨actorRow, actorAt, actorComponent⟩ := compatible.2
    have provided : Provided component key := by
      have same := Option.some.inj (present.symm.trans actorAt)
      rw [← actorComponent, ← same]
      exact declared
    let input : CompatibleProvision.Gamma ops actor component := ⟨before, compatible⟩
    let output := CompatibleProvision.setSlot key provided (some value) input
    have bound : tableAt before actor key = none := by simp [tableAt, present, absent]
    apply run_stage (program := program) (actor := actor) (observe := observe) (component := component) input output (CompatibleProvision.restrict key provided) PUnit.unit
    · simp [Head.provision, ScopedEffects.provision, ofOperation, CompatibleProvision.provision, input, output, bound]
    · exact terminal
    · intro following selected
      exact continues (.provision key value) following (by simp [replyAt, action]) selected selected
  | operate _ actor code key name argument owner old value inverse reply action located called =>
    obtain ⟨route, routed, rfl, provider, present, payload⟩ := matching
    rw [recipeStep_eq _ _ _ _ _ action]
    simp only [recipeStepAt, routed]
    have ownerAndValue := bound_by_location located
    let input : BoundOperation.Gamma ops actor component route.owner route.provider key :=
      ⟨before, compatible, ⟨compatible.1, provider, present, payload⟩, ownerAndValue.1⟩
    let output := BoundOperation.setSlot route.provides (some value) input
    apply run_stage (program := program) (actor := actor) (observe := observe) (component := component) input output (BoundOperation.liftMap route.provides inverse) reply
    · exact (BoundOperation.operation_success_iff route.provides _ _ _ _ _).mpr
        ⟨old, value, inverse, ownerAndValue.2, called, rfl, rfl⟩
    · exact terminal
    · intro following selected
      exact continues (.operation key name reply) following
        (by simp [replyAt, action, located, called]) selected selected
  | instantiate _ actor code payload child action ready =>
    have draw : choices.draw code history = child := matching
    subst child
    rw [recipeStep_eq _ _ _ _ _ action]
    simp only [recipeStepAt]
    let newborn := choices.draw code history
    let input : AllocationDomains.Before ops actor newborn component payload := ⟨before, compatible, ready⟩
    apply run_stage (program := program) (actor := actor) (observe := observe) (component := component)
      input (AllocationDomains.allocate input) (some ∘ AllocationDomains.inverse) PUnit.unit rfl result terminal
    intro following selected
    exact continues (.child newborn) following (by simp [replyAt, action, newborn]) selected selected

/-- Primitive failure on a retained native probe. When an allocation
lacks a reservation, that probe is outside its input domain. -/
inductive ChosenFailure (program : Code → Instruction Name ops Code) (actor : Name)
    (choices : Choices ops Name Code) (code : Code) (state : R) : Prop where
  | provide {key : Key} {value : V key} :
    (program code).action = .provide key value → tableAt state actor key ≠ none →
    ChosenFailure program actor choices code state
  | operate {key : Key} {name : ops.Name key} {argument : ops.Argument key name}
      (route : Route Name Code key) :
    (program code).action = .operate key name argument → choices.route key = some route →
    (∃ provider, state route.owner = some provider ∧ provider.component = route.provider) →
    bindingOwner state actor key = some route.owner → replyAt program actor none code state = none →
    ChosenFailure program actor choices code state

theorem ChosenFailure.no_landing {choices : Choices ops Name Code} {state after : R}
    {token : Inverse Name V} {next : Option Code}
    (failure : ChosenFailure program actor choices code state)
    (landed : Land program actor code state after token next) : False := by
  cases failure with
  | @provide key value action occupied =>
    cases landed with
    | provide _ _ _ row used given instructed present _ vacant =>
      cases action.symm.trans instructed
      exact occupied (by simp [tableAt, present, vacant])
    | unit _ _ _ instructed | operate _ _ _ _ _ _ _ _ _ _ _ instructed _ _
      | instantiate _ _ _ _ _ instructed _ => cases action.symm.trans instructed
  | @operate key name argument route action _ _ _ failed =>
    cases landed with
    | operate _ _ _ used calledWith arg _ _ _ _ _ instructed located called =>
      cases action.symm.trans instructed
      simp [replyAt, action, located, called] at failed
    | unit _ _ _ instructed | provide _ _ _ _ _ _ instructed _ _ _
      | instantiate _ _ _ _ _ instructed _ => cases action.symm.trans instructed

private theorem reflect_failure (choices : Choices ops Name Code) (lawful : OperationsLawful ops observe)
    (grammar : Mediated program component code) (history : List (Outcome Name ops))
    {state : R} (compatible : CompatibleProvision.Compatible ops actor component state)
    (failure : ChosenFailure program actor choices code state) :
    Runs program actor observe (Interface component) (recipe choices lawful grammar history) state none := by
  rw [recipe_eq]
  cases failure with
  | @provide key value action occupied =>
    rw [recipeStep_eq _ _ _ _ _ action]
    simp only [recipeStepAt]
    apply Runs.failed compatible
    cases binding : tableAt state actor key with
    | none => exact False.elim (occupied binding)
    | some _ => simp [Head.provision, ScopedEffects.provision, ofOperation, CompatibleProvision.provision, binding]
  | @operate key name argument route action selected provider routed failed =>
    obtain ⟨row, found, payload⟩ := provider
    rw [recipeStep_eq _ _ _ _ _ action]
    simp only [recipeStepAt, selected]
    apply Runs.failed ⟨compatible, ⟨compatible.1, row, found, payload⟩, routed⟩
    cases bound : tableAt state route.owner key with
    | none => simp [Head.operate, ScopedEffects.operate, ofOperation, BoundOperation.liftOperation, bound]
    | some value =>
      cases called : (ops.operation key name argument).run value with
      | none => simp [Head.operate, ScopedEffects.operate, ofOperation, BoundOperation.liftOperation, bound, called]
      | some returned =>
        obtain ⟨updated, saved, outcome⟩ := returned
        simp [replyAt, action, location, routed, bound, called] at failed

/-- The actual calculation at prescribed draws and provider scopes,
including the final cut of its successful prefix when a call fails. -/
inductive ChosenRun (program : Code → Instruction Name ops Code) (actor : Name)
    (choices : Choices ops Name Code) : List (Outcome Name ops) → Code → R → R → Bool → Prop
  | failed {history code state} (failure : ChosenFailure program actor choices code state) :
      ChosenRun program actor choices history code state state false
  | last {history code before after token}
      (landed : Land program actor code before after token none)
      (matching : Matches choices history code before token) :
      ChosenRun program actor choices history code before after true
  | next {history code following before middle after token reply finished}
      (landed : Land program actor code before middle token (some following))
      (matching : Matches choices history code before token)
      (replied : nativeReply program actor (choices.draw code history) code before = some reply)
      (rest : ChosenRun program actor choices (reply :: history) following middle after finished) :
      ChosenRun program actor choices history code before after finished

theorem ChosenRun.keeps {choices : Choices ops Name Code} {history : List (Outcome Name ops)}
    {before after : R} {finished : Bool} (run : ChosenRun program actor choices history code before after finished) :
    ScopedRollback.Keeps ops before after := by
  induction run with
  | failed => exact .refl _ _
  | last landed _ => exact .land landed
  | next landed _ _ _ ih => exact (ScopedRollback.Keeps.land landed).trans ih

theorem ChosenRun.first {choices : Choices ops Name Code} {history : List (Outcome Name ops)}
    {before final : R} {finished : Bool}
    (chosen : ChosenRun program actor choices history code before final finished) :
    ChosenFailure program actor choices code before ∨
      ∃ middle token next, Land program actor code before middle token next ∧
        Matches choices history code before token ∧ ScopedRollback.Keeps ops middle final := by
  cases chosen with
  | failed failure => exact .inl failure
  | last landed matched => exact .inr ⟨_, _, _, landed, matched, .refl _ _⟩
  | next landed matched _ rest => exact .inr ⟨_, _, _, landed, matched, rest.keeps⟩

theorem reflects_run {choices : Choices ops Name Code} {history : List (Outcome Name ops)}
    {before after : R} {finished : Bool} (run : ChosenRun program actor choices history code before after finished)
    (grammar : Mediated program component code) (lawful : OperationsLawful ops observe)
    (compatible : CompatibleProvision.Compatible ops actor component before) :
    Runs program actor observe (Interface component) (recipe choices lawful grammar history) before
      (if finished then some after else none) := by
  induction run with
  | failed failure => exact reflect_failure choices lawful grammar _ compatible failure
  | last landed matched =>
    apply reflect_landing choices lawful grammar _ landed compatible matched _ (fun _ => rfl)
    intro _ _ _ _ impossible
    cases impossible
  | next landed matched replied rest ih =>
    apply reflect_landing choices lawful grammar _ landed compatible matched _
    · intro impossible
      cases impossible
    · intro reply following result selected same
      cases Option.some.inj (replied.symm.trans result)
      cases Option.some.inj same
      exact ih (successor grammar ⟨_, selected⟩)
        ((ScopedRollback.Stable.provision ops actor component).land landed compatible)

/-- Initial compatibility and the actual prescribed native landings suffice
to admit the computation. All forward continuation links are synthesized
by compilation, including those determined by arbitrary operation outcomes. -/
theorem admits_native_run {choices : Choices ops Name Code} {history : List (Outcome Name ops)}
    {before after : R} {finished : Bool} (run : ChosenRun program actor choices history code before after finished)
    (grammar : Mediated program component code) (lawful : OperationsLawful ops observe)
    (compatible : CompatibleProvision.Compatible ops actor component before) :
    let admitted := admit (actor := actor) choices lawful grammar history
    ∃ input : admitted.domain before, admitted.iterator.execute ⟨before, input⟩ =
      (if finished then some after else none) :=
  ScopedAdmission.runs_iff.mp (reflects_run run grammar lawful compatible)

private theorem extract_stage {source target : R → Prop} {O : Type u}
    {head : Head program actor observe (Interface component) code source target O}
    {tail : ∀ reply next, (program code).next (head.reply reply) = some next →
      Unlinked program actor observe (Interface component) next}
    {choices : Choices ops Name Code} {history : List (Outcome Name ops)}
    {before : R} {result : Option R}
    (run : Runs program actor observe (Interface component) (.stage head tail) before result)
    (fails : ∀ (input : State source), head.effect.run input = none →
      ChosenFailure program actor choices code input.val)
    (choicesMatch : ∀ (input : State source) {after token next},
      Land program actor code input.val after token next → capturedChild token = head.draw →
      Matches choices history code input.val token)
    (continues : ∀ reply next (selected : (program code).next (head.reply reply) = some next) state output,
      Runs program actor observe (Interface component) (tail reply next selected) state output →
      ∃ last finished, ChosenRun program actor choices (head.reply reply :: history) next state last finished ∧
        output = (if finished then some last else none)) :
    ∃ last finished, ChosenRun program actor choices history code before last finished ∧
      result = (if finished then some last else none) := by
  cases run with
  | failed scope called => exact ⟨_, false, .failed (fails ⟨before, scope⟩ called), rfl⟩
  | last scope output saved reply called terminal =>
    obtain ⟨token, landed, _, drawn, _⟩ := head.realizes.sound ⟨before, scope⟩ output saved reply called
    have actual := choicesMatch ⟨before, scope⟩ landed drawn
    rw [terminal] at landed
    exact ⟨_, true, .last landed actual, rfl⟩
  | next scope output saved reply called following selected continued =>
    obtain ⟨token, landed, _, drawn, replied⟩ := head.realizes.sound ⟨before, scope⟩ output saved reply called
    have actual := choicesMatch ⟨before, scope⟩ landed drawn
    have sameReply := chosen_reply_at landed actual
    rw [drawn, replied] at sameReply
    rw [selected] at landed
    obtain ⟨last, finished, rest, reported⟩ := continues _ _ selected _ _ continued
    exact ⟨last, finished, .next landed actual sameReply.symm rest, reported⟩

/-- Recover the precisely selected native computation from an admitted
recipe, including its actual endpoint before a partial failure. -/
theorem extracts_run (choices : Choices ops Name Code) (lawful : OperationsLawful ops observe)
    (grammar : Mediated program component code) (history : List (Outcome Name ops))
    {before : R} {result : Option R}
    (run : Runs program actor observe (Interface component) (recipe choices lawful grammar history) before result) :
    ∃ last finished, ChosenRun program actor choices history code before last finished ∧
      result = (if finished then some last else none) := by
  have extract (current : Code) (acc : Acc (Selected program) current)
      (grammar : Mediated program component current) (history : List (Outcome Name ops))
      (before : R) (result : Option R)
      (run : Runs program actor observe (Interface component) (recipe choices lawful grammar history) before result) :
      ∃ last finished, ChosenRun program actor choices history current before last finished ∧
        result = (if finished then some last else none) := by
    induction acc generalizing history before result with
    | intro current smaller ih =>
      rw [recipe_eq] at run
      cases action : (program current).action with
      | unit =>
        rw [recipeStep_eq _ _ _ _ _ action] at run
        simp only [recipeStepAt] at run
        refine extract_stage run ?_ ?_ ?_
        · intro input failed
          exact False.elim (Option.noConfusion failed)
        · intro input after token next landed _
          cases landed <;> simp_all [Matches]
        · intro reply next selected _ _ _
          have terminal : (program current).next .unit = none := by
            simpa only [Declared, action] using declared grammar
          change (program current).next .unit = some next at selected
          rw [terminal] at selected
          cases selected
      | provide key value =>
        rw [recipeStep_eq _ _ _ _ _ action] at run
        simp only [recipeStepAt] at run
        refine extract_stage run ?_ ?_ ?_
        · intro input failed
          apply ChosenFailure.provide action
          intro vacant
          simp [Head.provision, ScopedEffects.provision, ofOperation, CompatibleProvision.provision, vacant] at failed
        · intro input after token next landed _
          cases landed <;> simp_all [Matches]
        · intro reply next selected state output continued
          exact ih next ⟨.provision key value, selected⟩ _ _ state output continued
      | operate key name argument =>
        rw [recipeStep_eq _ _ _ _ _ action] at run
        cases routed : choices.route key with
        | none =>
          simp only [recipeStepAt, routed, unavailableHead] at run
          cases run with
          | failed outside _ | last outside _ _ _ _ _ | next outside _ _ _ _ _ _ _ => cases outside
        | some route =>
          simp only [recipeStepAt, routed] at run
          refine extract_stage run ?_ ?_ ?_
          · intro input failed
            refine .operate route action routed input.property.2.1.2 input.property.2.2 ?_
            cases slot : tableAt input.val route.owner key with
            | none => simp [replyAt, action, location, input.property.2.2, slot]
            | some value =>
              cases called : (ops.operation key name argument).run value with
              | none => simp [replyAt, action, location, input.property.2.2, slot, called]
              | some triple =>
                obtain ⟨updated, saved, reply⟩ := triple
                simp [Head.operate, ScopedEffects.operate, ofOperation, BoundOperation.liftOperation, slot, called] at failed
          · intro input after token next landed _
            cases landed with
            | operate _ _ _ used op arg owner before after inverse outcome instructed located called =>
              cases action.symm.trans instructed
              have same : owner = route.owner :=
                Option.some.inj ((bound_by_location located).1.symm.trans input.property.2.2)
              subst owner
              exact ⟨route, routed, rfl, input.property.2.1.2⟩
            | unit _ _ _ instructed | provide _ _ _ _ _ _ instructed _ _ _
              | instantiate _ _ _ _ _ instructed _ => cases action.symm.trans instructed
          · intro reply next selected state output continued
            exact ih next ⟨.operation key name reply, selected⟩ _ _ state output continued
      | instantiate child =>
        rw [recipeStep_eq _ _ _ _ _ action] at run
        simp only [recipeStepAt] at run
        refine extract_stage run ?_ ?_ ?_
        · intro input failed
          exact False.elim (Option.noConfusion failed)
        · intro input after token next landed drawn
          cases token <;> simp_all [Matches, Head.allocate, capturedChild]
        · intro reply next selected state output continued
          exact ih next ⟨.child (choices.draw current history), selected⟩ _ _ state output continued
  exact extract code (accessible grammar) grammar history before result run

/-- Admission is equivalent to the existence of the corresponding
native calculation or a native prefix ending in a genuine failed call. -/
theorem admits_iff_chosen (choices : Choices ops Name Code) (lawful : OperationsLawful ops observe)
    (grammar : Mediated program component code) (history : List (Outcome Name ops))
    {before : R} (compatible : CompatibleProvision.Compatible ops actor component before) :
    (admit (actor := actor) choices lawful grammar history).domain before ↔
      ∃ last finished, ChosenRun program actor choices history code before last finished := by
  constructor
  · intro admitted
    obtain ⟨last, finished, chosen, _⟩ :=
      extracts_run choices lawful grammar history (run_of_admitted _ ⟨before, admitted⟩)
    exact ⟨last, finished, chosen⟩
  · rintro ⟨last, finished, chosen⟩
    exact (admits_native_run chosen grammar lawful compatible).1

theorem recipe_confined (choices : Choices ops Name Code) (lawful : OperationsLawful ops observe)
    (grammar : Mediated program component code) (history : List (Outcome Name ops)) :
    ScopedConfinement.RecipeConfined component (recipe (actor := actor) choices lawful grammar history) := by
  have prove (current : Code) (acc : Acc (Selected program) current)
      (grammar : Mediated program component current) (history : List (Outcome Name ops)) :
      ScopedConfinement.RecipeConfined component (recipe (actor := actor) choices lawful grammar history) := by
    induction acc generalizing history with
    | intro current smaller ih =>
      rw [recipe_eq]
      cases action : (program current).action with
      | unit =>
        rw [recipeStep_eq _ _ _ _ _ action]
        simp only [recipeStepAt, ScopedConfinement.RecipeConfined]
        have terminal : (program current).next .unit = none := by
          simpa only [Declared, action] using declared grammar
        refine ⟨?_, ?_⟩
        · simpa only [ScopedConfinement.HeadConfined, action, Head.unit] using
            (ScopedConfinement.unit (actor := actor) (acting := component)
              (CompatibleProvision.Compatible ops actor component))
        · intro _ next continued
          change (program current).next .unit = some next at continued
          rw [terminal] at continued
          cases continued
      | provide key value =>
        rw [recipeStep_eq _ _ _ _ _ action]
        simp only [recipeStepAt, ScopedConfinement.RecipeConfined]
        have provided : Provided component key := by simpa only [Declared, action] using declared grammar
        refine ⟨?_, ?_⟩
        · simpa only [ScopedConfinement.HeadConfined, action, Head.provision] using
            ScopedConfinement.provision (ops := ops) (actor := actor) key provided value
        · intro _ next selected
          exact ih next ⟨.provision key value, selected⟩ _ _
      | operate key name argument =>
        rw [recipeStep_eq _ _ _ _ _ action]
        cases routed : choices.route key with
        | none =>
          simp only [recipeStepAt, routed, unavailableHead, ScopedConfinement.RecipeConfined]
          refine ⟨?_, fun impossible => nomatch impossible⟩
          simp only [ScopedConfinement.HeadConfined, action]
          exact ⟨fun input => False.elim input.property, fun input => False.elim input.property⟩
        | some route =>
          simp only [recipeStepAt, routed, ScopedConfinement.RecipeConfined]
          refine ⟨?_, ?_⟩
          · simpa only [ScopedConfinement.HeadConfined, action, Head.operate] using
              ScopedConfinement.operate (actor := actor) (owner := route.owner) (acting := component)
                key route.provides name argument
          · intro reply next selected
            exact ih next ⟨.operation key name reply, selected⟩ _ _
      | instantiate child =>
        rw [recipeStep_eq _ _ _ _ _ action]
        simp only [recipeStepAt, ScopedConfinement.RecipeConfined]
        refine ⟨?_, ?_⟩
        · simpa only [ScopedConfinement.HeadConfined, action] using
            ScopedConfinement.allocate (acting := component) (actor := actor) (observe := observe)
              (keys := Interface component) (choices.draw current history) action
        · intro _ next selected
          exact ih next ⟨.child (choices.draw current history), selected⟩ _ _
  exact prove code (accessible grammar) grammar history

theorem admit_confined (choices : Choices ops Name Code) (lawful : OperationsLawful ops observe)
    (grammar : Mediated program component code) (history : List (Outcome Name ops)) :
    ScopedConfinement.IteratorConfined component (admit (actor := actor) choices lawful grammar history).iterator :=
  ScopedConfinement.compile_confined (recipe_confined choices lawful grammar history)

end Cordis.Repairs.MediatedAdmission
