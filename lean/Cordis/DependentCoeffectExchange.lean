import Cordis.PaperObservationEquations

/-! The value-level exchange in Lemma 78 for the key-dependent operation
families of Definition 29. All original partial maps are retained. -/
namespace Cordis.DependentCoeffectExchange
open PartialCoeffectLifting PartialInverseObservation
open PartialCoeffectIndependenceContracts (tableSetoid)
open PartialMediatedIndependence (Generator forward)
open PartialIterators (stage)
open PartialIteratorRelationLaws (YieldRel observe)
open Coeffects (update update_same update_other)
open Iterators (OptionRel)

universe u
variable {Key : Type u} {Value : Key → Type u} [DecidableEq Key]

def singleton (key : Key) (value : Value key) : Table Value :=
  update (V := fun key => Option (Value key)) key (some value) (fun _ => none)

theorem related_singleton (relations : ∀ key, Setoid (Value key)) (key : Key)
    {left right : Value key} (related : (relations key).r left right) :
    (tableSetoid relations (fun _ => True)).r (singleton key left) (singleton key right) := by
  intro other _
  by_cases same : other = key
  · subst other
    simpa only [singleton, update_same, OptionRel] using related
  · simp [singleton, update_other, same, OptionRel]

private theorem singleton_related_value (relations : ∀ key, Setoid (Value key)) (key : Key)
    {left right : Value key}
    (compared : (tableSetoid relations (fun _ => True)).r (singleton key left) (singleton key right)) :
    (relations key).r left right := by
  simpa only [singleton, update_same, OptionRel] using compared key trivial

private theorem lift_inverse_singleton (key : Key)
    (inverse : PartialMap (Value key)) (value : Value key) :
    liftMap key inverse (singleton key value) = (inverse value).map (singleton key) := by
  cases applied : inverse value <;> simp [liftMap, singleton, applied, update_overwrite]

theorem inverse_related_from_lift (relations : ∀ key, Setoid (Value key)) (key : Key)
    {left right : PartialMap (Value key)}
    (compared : MapRelated (tableSetoid relations (fun _ => True)).r (liftMap key left) (liftMap key right)) :
    MapRelated (relations key).r left right := by
  intro input output related
  have lifted := compared (singleton key input) (singleton key output) (related_singleton relations key related)
  rw [lift_inverse_singleton, lift_inverse_singleton] at lifted
  cases first : left input <;> cases second : right output
  all_goals simp only [first, second, Option.map_none, Option.map_some, OptionRel] at lifted ⊢
  exact singleton_related_value relations key lifted

theorem lift_success (key : Key) {Outcome : Type u} (operation : Operation (Value key) Outcome)
    {input output : Value key} {inverse : PartialMap (Value key)} {outcome : Outcome}
    (called : operation.run input = some (output, inverse, outcome)) :
    (liftOperation key operation).run (singleton key input) =
      some (singleton key output, liftMap key inverse, outcome) := by
  simp [liftOperation, called, singleton, update_overwrite]

theorem lift_outcome (key : Key) {Outcome : Type u} (operation : Operation (Value key) Outcome)
    (input : Value key) (outcome : Outcome)
    (success : ((liftOperation key operation).run (singleton key input)).map
      (fun result => result.2.2) = some outcome) :
    ∃ output inverse, operation.run input = some (output, inverse, outcome) := by
  cases returned : operation.run input with
  | none => simp [liftOperation, singleton, returned] at success
  | some triple =>
    obtain ⟨output, inverse, result⟩ := triple
    have same : result = outcome := by simpa [liftOperation, singleton, returned] using success
    subst result
    exact ⟨output, inverse, rfl⟩

theorem stage_success (key : Key) {Outcome : Type u} (operation : Operation (Value key) Outcome)
    {input output : Value key} {inverse : PartialMap (Value key)} {outcome : Outcome}
    (called : operation.run input = some (output, inverse, outcome)) :
    (stage (liftOperation key operation) (fun _ => none)).run (singleton key input) =
      some (singleton key output, liftMap key inverse, none) :=
  (PartialIterators.stage_success_iff _ _ _ _ _ _).mpr ⟨outcome, lift_success key operation called, rfl⟩

/-- The identity foreign word in Definition 44's self-independence clause
forces each successfully captured inverse to respect the observation. -/
theorem capture_respects (operations : PaperEffectEquations.CoeffectOperations Value)
    (relations : ∀ key, Setoid (Value key)) (key : Key) (name : operations.Name key)
    (argument : operations.Argument key name)
    (laws : PaperObservationEquations.IndependentOperations operations
      (tableSetoid relations (fun _ => True)) key key name name)
    {input output : Value key} {inverse : PartialMap (Value key)}
    {outcome : operations.Outcome key name}
    (called : (operations.operation key name argument).run input = some (output, inverse, outcome)) :
    MapRelated (relations key).r inverse inverse := by
  let operation := operations.operation key name argument
  let root := stage (liftOperation key operation) (fun _ => none)
  let observation := tableSetoid relations (fun _ => True)
  have self := laws.1 argument argument
  change PartialObservedIteratorIndependence.Independent observation root root at self
  have yielded := self.left_yield root .root some .identity (singleton key input) (singleton key input) rfl
  have run := stage_success key operation called
  have lifted : MapRelated observation.r (liftMap key inverse) (liftMap key inverse) := by
    simpa [root, observe, run, YieldRel, OptionRel] using yielded
  exact inverse_related_from_lift relations key lifted

/-- Applying one defined foreign operation generator on the same binding
preserves whether the local call yields, its exact typed outcome, and the
observation of the partial inverse it returns. This includes a foreign
inverse captured at any successful application of that operation. -/
theorem yield_after_generator (operations : PaperEffectEquations.CoeffectOperations Value)
    (relations : ∀ key, Setoid (Value key)) (key : Key)
    (localName foreignName : operations.Name key)
    (localArg : operations.Argument key localName) (foreignArg : operations.Argument key foreignName)
    (laws : PaperObservationEquations.IndependentOperations operations
      (tableSetoid relations (fun _ => True)) key key localName foreignName)
    {move : PartialMap (Value key)}
    (generator : PartialCoeffectIndependenceContracts.OperationGenerator
      (operations.operation key foreignName foreignArg) move)
    {before after : Value key} (moved : move before = some after) :
    OptionRel (fun new old => MapRelated (relations key).r new.2.1 old.2.1 ∧ new.2.2 = old.2.2)
      ((operations.operation key localName localArg).run after)
      ((operations.operation key localName localArg).run before) := by
  let localOp := operations.operation key localName localArg
  let foreignOp := operations.operation key foreignName foreignArg
  let localStage := stage (liftOperation key localOp) (fun _ => none)
  let foreignStage := stage (liftOperation key foreignOp) (fun _ => none)
  let observation := tableSetoid relations (fun _ => True)
  have foreignLifted : Generator foreignStage (liftMap key move) ∧
      PaperObservationEquations.OperationMonoid operations key foreignName (liftMap key move) := by
    cases generator with
    | forward =>
      have forwardLift : liftMap key (PartialCoeffectLifting.forward foreignOp) =
          PartialCoeffectLifting.forward (liftOperation key foreignOp) := by
        funext table
        cases loaded : table key with
        | none => simp [liftMap, PartialCoeffectLifting.forward, liftOperation, loaded]
        | some value =>
          cases called : foreignOp.run value <;>
            simp [liftMap, PartialCoeffectLifting.forward, liftOperation, loaded, called]
      rw [forwardLift]
      refine ⟨?_, .generator ⟨foreignArg, .forward⟩⟩
      have stageForward : PartialMediatedIndependence.forward foreignStage =
          PartialCoeffectLifting.forward (liftOperation key foreignOp) := by
        funext table
        cases called : (liftOperation key foreignOp).run table <;>
          simp [foreignStage, PartialMediatedIndependence.forward, PartialCoeffectLifting.forward,
            PartialIterators.stage, PartialIterators.Iterator.run, called]
      rw [← stageForward]
      exact .forward .root
    | inverse input output _ outcome called =>
      refine ⟨.inverse .root (singleton key input) (singleton key output) _ none
        (stage_success key foreignOp called), .generator ⟨foreignArg, ?_⟩⟩
      exact .inverse (singleton key input) (singleton key output) _ outcome
        (lift_success key foreignOp called)
  have applied : liftMap key move (singleton key before) = some (singleton key after) := by
    rw [lift_inverse_singleton, moved]
    rfl
  have independent := laws.1 localArg foreignArg
  change PartialObservedIteratorIndependence.Independent observation localStage foreignStage at independent
  have yields := independent.left_yield localStage .root (liftMap key move) (.generator foreignLifted.1) _ _ applied
  have outcomes := laws.2.1 localArg _ foreignLifted.2 _ _ applied
  change ((liftOperation key localOp).run (singleton key after)).map _ =
    ((liftOperation key localOp).run (singleton key before)).map _ at outcomes
  change OptionRel _ (localOp.run after) (localOp.run before)
  cases prior : localOp.run before with
  | none =>
    have absent : (liftOperation key localOp).run (singleton key before) = none := by
      simp [liftOperation, singleton, prior]
    cases later : localOp.run after with
    | none => trivial
    | some output =>
      obtain ⟨value, inverse, outcome⟩ := output
      rw [lift_success key localOp later, absent] at outcomes
      contradiction
  | some output =>
    obtain ⟨value, inverse, outcome⟩ := output
    have original := lift_success key localOp prior
    rw [original] at outcomes
    obtain ⟨newValue, newInverse, later⟩ := lift_outcome key localOp after outcome outcomes
    rw [later]
    have related : MapRelated observation.r (liftMap key newInverse) (liftMap key inverse) := by
      simpa [localStage, observe, stage_success key localOp prior, stage_success key localOp later,
        YieldRel, OptionRel] using yields
    exact ⟨inverse_related_from_lift relations key related, rfl⟩

/-- Successful words may interleave different callbacks and saved inverses
at a key. Each letter is generated by a real coeffect operation, and the
key's Definition 46 witness supplies the law for that letter and the local
instruction. -/
theorem yield_after_generated_at_key (operations : PaperEffectEquations.CoeffectOperations Value)
    (relations : ∀ key, Setoid (Value key)) (key : Key)
    (localName : operations.Name key) (localArg : operations.Argument key localName)
    (lawful : PaperObservationEquations.CommutativeKey operations
      (tableSetoid relations (fun _ => True)) key)
    {move : PartialMap (Value key)}
    (generated : PartialMapClosure.Generated
      (fun map => ∃ foreignName foreignArg, PartialCoeffectIndependenceContracts.OperationGenerator
        (operations.operation key foreignName foreignArg) map) move) :
    ∀ {before after}, move before = some after →
      OptionRel (fun new old => MapRelated (relations key).r new.2.1 old.2.1 ∧ new.2.2 = old.2.2)
        ((operations.operation key localName localArg).run after)
        ((operations.operation key localName localArg).run before) := by
  induction generated with
  | identity =>
    intro before after moved
    cases Option.some.inj moved
    cases called : (operations.operation key localName localArg).run before with
    | none => trivial
    | some result =>
      obtain ⟨output, inverse, outcome⟩ := result
      exact ⟨capture_respects operations relations key localName localArg (lawful localName localName) called, rfl⟩
  | generator native =>
    obtain ⟨foreignName, foreignArg, generator⟩ := native
    exact yield_after_generator operations relations key localName foreignName localArg foreignArg
      (lawful localName foreignName) generator
  | composition _ _ afterIH beforeIH =>
    intro before after moved
    obtain ⟨middle, first, second⟩ := Option.bind_eq_some_iff.mp moved
    apply OptionRel.trans _ (afterIH second) (beforeIH first)
    intro new old prior lastStep firstStep
    refine ⟨?_, lastStep.2.trans firstStep.2⟩
    intro input output related
    exact OptionRel.trans (R := (relations key).r) (fun _ _ _ => (relations key).trans)
      (lastStep.1 input input ((relations key).refl input)) (firstStep.1 input output related)

/-- Definition 44 implies that two successive successful calls at one key can
be reversed. Equation (41) derives both swapped successes and preserves each
outcome in its own type. The resulting values and the captured partial inverse
maps are related by the observation at that key. -/
theorem exchange_same_key (operations : PaperEffectEquations.CoeffectOperations Value)
    (relations : ∀ key, Setoid (Value key))
    (key : Key) (firstName secondName : operations.Name key)
    (firstArg : operations.Argument key firstName) (secondArg : operations.Argument key secondName)
    (laws : PaperObservationEquations.IndependentOperations operations
      (tableSetoid relations (fun _ => True)) key key firstName secondName)
    {before afterFirst finalOriginal : Value key}
    {firstInverse secondInverse : PartialMap (Value key)}
    {firstOutcome : operations.Outcome key firstName} {secondOutcome : operations.Outcome key secondName}
    (firstCalled : (operations.operation key firstName firstArg).run before =
      some (afterFirst, firstInverse, firstOutcome))
    (secondCalled : (operations.operation key secondName secondArg).run afterFirst =
      some (finalOriginal, secondInverse, secondOutcome)) :
    ∃ afterSecond secondBefore finalReordered firstAfter,
      (operations.operation key secondName secondArg).run before = some (afterSecond, secondBefore, secondOutcome) ∧
      (operations.operation key firstName firstArg).run afterSecond = some (finalReordered, firstAfter, firstOutcome) ∧
      (relations key).r finalReordered finalOriginal ∧
      MapRelated (relations key).r secondInverse secondBefore ∧
      MapRelated (relations key).r firstAfter firstInverse := by
  let leftOperation := operations.operation key firstName firstArg
  let rightOperation := operations.operation key secondName secondArg
  let leftLift := liftOperation key leftOperation
  let rightLift := liftOperation key rightOperation
  let observation := tableSetoid relations (fun _ => True)
  have firstLift := lift_success key leftOperation firstCalled
  have secondLift := lift_success key rightOperation secondCalled
  have stableSecond := laws.2.2 secondArg (PartialCoeffectLifting.forward leftLift)
    (.generator ⟨firstArg, .forward⟩) (singleton key before) (singleton key afterFirst)
    (congrArg (fun result => result.map Prod.fst) firstLift)
  change (rightLift.run (singleton key afterFirst)).map _ =
    (rightLift.run (singleton key before)).map _ at stableSecond
  rw [show rightLift.run (singleton key afterFirst) = _ from secondLift] at stableSecond
  obtain ⟨afterSecond, secondBefore, secondReordered⟩ :=
    lift_outcome key rightOperation before secondOutcome stableSecond.symm
  have stableFirst := laws.2.1 firstArg (PartialCoeffectLifting.forward rightLift)
    (.generator ⟨secondArg, .forward⟩) (singleton key before) (singleton key afterSecond)
    (congrArg (fun result => result.map Prod.fst) (lift_success key rightOperation secondReordered))
  change (leftLift.run (singleton key afterSecond)).map _ =
    (leftLift.run (singleton key before)).map _ at stableFirst
  rw [show leftLift.run (singleton key before) = _ from firstLift] at stableFirst
  obtain ⟨finalReordered, firstAfter, firstReordered⟩ :=
    lift_outcome key leftOperation afterSecond firstOutcome stableFirst
  have independent := laws.1 firstArg secondArg
  let leftStage := stage leftLift (fun _ => none)
  let rightStage := stage rightLift (fun _ => none)
  change PartialObservedIteratorIndependence.Independent observation leftStage rightStage at independent
  have leftGenerated : PartialMapClosure.Generated (Generator leftStage) (forward leftStage) :=
    .generator (.forward .root)
  have rightGenerated : PartialMapClosure.Generated (Generator rightStage) (forward rightStage) :=
    .generator (.forward .root)
  have leftRun := stage_success key leftOperation firstCalled
  have rightRun := stage_success key rightOperation secondReordered
  have leftRunAfter := stage_success key leftOperation firstReordered
  have rightRunAfter := stage_success key rightOperation secondCalled
  have leftForward : forward leftStage (singleton key before) = some (singleton key afterFirst) :=
    congrArg (fun result => result.map Prod.fst) leftRun
  have rightForward : forward rightStage (singleton key before) = some (singleton key afterSecond) :=
    congrArg (fun result => result.map Prod.fst) rightRun
  have rightThenLeft : forward leftStage (singleton key afterSecond) = some (singleton key finalReordered) :=
    congrArg (fun result => result.map Prod.fst) leftRunAfter
  have leftThenRight : forward rightStage (singleton key afterFirst) = some (singleton key finalOriginal) :=
    congrArg (fun result => result.map Prod.fst) rightRunAfter
  have commuted := independent.commute _ leftGenerated _ rightGenerated
    (singleton key before) (singleton key before) (observation.refl _)
  change OptionRel observation.r ((forward rightStage (singleton key before)).bind (forward leftStage))
    ((forward leftStage (singleton key before)).bind (forward rightStage)) at commuted
  rw [rightForward, leftForward, Option.bind_some, Option.bind_some, rightThenLeft, leftThenRight] at commuted
  have rightYield := independent.right_yield rightStage .root _ leftGenerated _ _ leftForward
  have leftYield := independent.left_yield leftStage .root _ rightGenerated _ _ rightForward
  change YieldRel observation (observe rightStage (singleton key afterFirst)) (observe rightStage (singleton key before))
    at rightYield
  change YieldRel observation (observe leftStage (singleton key afterSecond)) (observe leftStage (singleton key before))
    at leftYield
  have rightCaptures : MapRelated observation.r (liftMap key secondInverse) (liftMap key secondBefore) := by
    simpa [rightStage, rightLift, observe, rightRunAfter, rightRun, YieldRel, OptionRel] using rightYield
  have leftCaptures : MapRelated observation.r (liftMap key firstAfter) (liftMap key firstInverse) := by
    simpa [leftStage, leftLift, observe, leftRunAfter, leftRun, YieldRel, OptionRel] using leftYield
  exact ⟨afterSecond, secondBefore, finalReordered, firstAfter, secondReordered, firstReordered,
    singleton_related_value relations key commuted, inverse_related_from_lift relations key rightCaptures,
    inverse_related_from_lift relations key leftCaptures⟩

end Cordis.DependentCoeffectExchange
