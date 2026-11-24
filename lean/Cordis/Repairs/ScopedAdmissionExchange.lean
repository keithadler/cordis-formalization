import Cordis.Repairs.ScopedIteratorGenerators

/-! Admission of the selected native calculation during exchanges.
The successful prefix supplies its complete reservation requirement,
including births after the last head of a generated transformation. -/
namespace Cordis.Repairs.ScopedAdmissionExchange
open TypedRegistry MediatedAdmission PairwiseSlots
open PaperEffectEquations (CoeffectOperations)
open PartialCoeffectIndependenceContracts (tableSetoid)
open PairwiseAllocation (DrawCompatible)
open PairwiseControl (Control)
open PairwiseNativeWords
open ScopedIteratorObservation ScopedIteratorGenerators
open PairwiseMixed (runMixed ordinaryPart controlPart StampedRelated)
open Iterators (OptionRel)

universe u
variable {Name Key Code : Type u} {V : Key → Type u}
variable [DecidableEq Name] [DecidableEq Key] {ops : CoeffectOperations V}
local notation "R" => Registry Name V Code
local notation "SR" => PairwiseControl.Stamped Name V Code
variable {program : Code → Instruction Name ops Code}
variable {actor foreignActor : Name} {component foreignComponent : Calculus.Component Key Code} {code : Code}
variable {choices : Choices ops Name Code} {before after : Registry Name V Code}

/-- Every row added before the chosen calculation finishes or fails
must coexist with the children of the foreign word. -/
def Reservations (before final : R) (foreign : List (Control Name Key Code)) : Prop :=
  ∀ child row, before child = none → final child = some row →
    ∀ parent other payload stamp, Control.birth parent other payload stamp ∈ foreign →
      DrawCompatible child other row.component payload

omit [DecidableEq Name] in
theorem Reservations.tail {middle final : R} {foreign : List (Control Name Key Code)}
    (earlier : ScopedRollback.Keeps ops before middle) (reservations : Reservations before final foreign) :
    Reservations middle final foreign := by
  intro child row vacant present parent other declared stamp member
  have initiallyVacant : before child = none := by
    cases first : before child with
    | none => rfl
    | some prior =>
      obtain ⟨_, existsAtMiddle, _⟩ := earlier.row child prior first
      rw [vacant] at existsAtMiddle
      cases existsAtMiddle
  exact reservations child row initiallyVacant present parent other declared stamp member

/-- The check of a single selected birth follows from the requirement at
the end of its whole chosen calculation. Later successful landings keep
that row and its declared provisions, even when the final call fails. -/
theorem Reservations.birth {middle final : R} {foreign : List (Control Name Key Code)}
    {child : Name} {payload : Calculus.Component Key Code} {next : Option Code}
    (landed : Land program actor code before middle (.retire child) next)
    (action : (program code).action = .instantiate payload)
    (suffix : ScopedRollback.Keeps ops middle final) (reservations : Reservations before final foreign) :
    ∀ parent other declared stamp, Control.birth parent other declared stamp ∈ foreign →
      DrawCompatible child other payload declared := by
  cases landed with
  | instantiate _ _ _ actual _ chosen ready =>
    have same := Action.instantiate.inj (chosen.symm.trans action)
    subst actual
    obtain ⟨row, present, fields, _, _⟩ := suffix.row child (fresh payload (some actor)) (by simp [put])
    simpa only [fields] using reservations child row ready.1 present

/-- Both kinds of native primitive failure retain their input scopes
after a separated foreign word. Provider identity follows from the actual
retained row and committed route at the failed call. -/
theorem failure_after_foreign (observe : ∀ key, Setoid (V key))
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (different : actor ≠ foreignActor) (separate : Transposition.Separated component foreignComponent)
    (grammar : Mediated program component code)
    (scope : CompatibleProvision.Compatible ops actor component before)
    (failure : ChosenFailure program actor choices code before)
    (foreign : NativeWord program foreignActor foreignComponent before after) :
    ChosenFailure program actor choices code after := by
  obtain ⟨row, found, payload⟩ := scope.2
  cases failure with
  | @provide key value action occupied =>
    have provided : component.provides key = true := by
      simpa only [Declared, action] using declared grammar
    obtain ⟨map, generated, projected⟩ := projects_native_word foreign
    have unchanged := generated_keeps_own_slot ops provided different separate generated _ _ projected
    exact .provide action (fun vacant => occupied (unchanged.symm.trans vacant))
  | @operate key name argument route action selected provider routed failed =>
    obtain ⟨prior, present, priorPayload⟩ := provider
    obtain ⟨current, kept, keptPayload, _, _⟩ := foreign.keeps.row route.owner prior present
    have access : component.provides key = true ∨ component.requires key = true := by
      have iface : Interface component key := by
        simpa only [Declared, action] using declared grammar
      rcases iface with required | provided
      · exact .inr required
      · exact .inl provided
    exact .operate route action selected ⟨current, kept, keptPayload.trans priorPayload⟩
      ((foreign.keeps.bindingOwner found key).trans routed)
      (operation_failure_after_native_word observe laws action found (payload.symm ▸ access)
        (payload.symm ▸ separate) routed failed foreign)

private theorem failure_after_related (observe : ∀ key, Setoid (V key))
    (respect : ∀ key, PaperObservationEquations.OperationRespects ops key (observe key).r)
    (related : PairwisePrograms.Related (ops := ops) observe before after)
    (failure : ChosenFailure program actor choices code before) :
    ChosenFailure program actor choices code after := by
  cases failure with
  | @provide key value action occupied =>
    apply ChosenFailure.provide action
    intro vacant
    have slots := PairwiseRegistry.slot_related observe related actor key
    rw [vacant] at slots
    cases bound : tableAt before actor key with
    | none => exact occupied bound
    | some _ => simp [bound, OptionRel] at slots
  | @operate key name argument route action selected provider routed failed =>
    obtain ⟨row, found, payload⟩ := provider
    obtain ⟨other, otherFound, otherPayload⟩ := PairwisePrograms.related_component related found
    have newRoute := (PairwisePrograms.related_bindingOwner related actor key).symm.trans routed
    refine .operate route action selected ⟨other, otherFound, otherPayload.trans payload⟩ newRoute ?_
    have slots := PairwiseRegistry.slot_related observe related route.owner key
    cases a : tableAt before route.owner key <;> cases b : tableAt after route.owner key <;>
      simp only [a, b, OptionRel] at slots
    · simp [replyAt, action, location, newRoute, b]
    · rename_i input otherInput
      have calls := respect key name argument input otherInput slots
      cases first : (ops.operation key name argument).run input with
      | none =>
        rw [first] at calls
        cases second : (ops.operation key name argument).run otherInput with
        | none => simp [replyAt, action, location, newRoute, b, second]
        | some _ => simp [second, OptionRel] at calls
      | some result =>
        obtain ⟨output, saved, outcome⟩ := result
        simp [replyAt, action, location, routed, a, first] at failed

private theorem matches_after_foreign {observe : ∀ key, Setoid (V key)}
    {foreignAfter : R} {history : List (Outcome Name ops)} {token otherToken : Inverse Name V}
    (kept : ScopedRollback.Keeps ops before foreignAfter)
    (related : PairwisePrograms.Related (ops := ops) observe foreignAfter after)
    (captured : PairwiseForward.CaptureRelated observe token otherToken)
    (matched : Matches choices history code before token) :
    Matches choices history code after otherToken := by
  cases captured with
  | unit | restrict | retire => exact matched
  | operate owner key _ =>
    obtain ⟨route, chosen, rfl, row, found, payload⟩ := matched
    obtain ⟨current, inForeign, currentPayload, _, _⟩ := kept.row route.owner row found
    obtain ⟨other, otherFound, otherPayload⟩ := PairwisePrograms.related_component related inForeign
    exact ⟨route, chosen, rfl, other, otherFound, otherPayload.trans (currentPayload.trans payload)⟩

/-- Transport the complete selected calculation, including its final
primitive failure when there is one. Reservation checks use every actual
birth in its successful prefix. The foreign word follows that prefix to
the matched cuts, preserving routes, outcomes, and later draw choices. -/
theorem chosen_after_word (observe : ∀ key, Setoid (V key))
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, PaperObservationEquations.OperationRespects ops key (observe key).r)
    (different : actor ≠ foreignActor) (separate : Transposition.Separated component foreignComponent)
    (foreign : List (Letter program foreignActor))
    (origins : ∀ letter ∈ foreign, letter.origin_has foreignComponent)
    (stamp : Nat)
    (later : ∀ child earlier, Control.retire child earlier ∈ controlPart (words foreign) → earlier < stamp)
    {history : List (Outcome Name ops)} {first final : R} {finished : Bool}
    (chosen : ChosenRun program actor choices history code first final finished)
    (grammar : Mediated program component code)
    (scope : CompatibleProvision.Compatible ops actor component first)
    (foreignScope : ∃ row, first foreignActor = some row ∧ row.component = foreignComponent)
    (live : Name → Option Nat) {foreignAfter alternate : SR}
    (ready : ∀ letter ∈ foreign, letter.ready first)
    (initial : StampedRelated ops observe (first, live) (first, live))
    (executed : runMixed (words foreign) (first, live) = some foreignAfter)
    (related : StampedRelated ops observe foreignAfter alternate)
    (reservations : Reservations first final (controlPart (words foreign))) :
    ∃ moved, ChosenRun program actor choices history code alternate.1 moved finished := by
  induction chosen generalizing live foreignAfter alternate with
  | failed failure =>
    obtain ⟨foreignRow, foreignFound, foreignPayload⟩ := foreignScope
    have native := native_word_of_run foreign foreignFound foreignPayload ready origins executed
    have kept := failure_after_foreign observe laws different separate grammar scope failure native
    exact ⟨_, .failed (failure_after_related observe respect related.2 kept)⟩
  | last landed matched =>
    obtain ⟨row, found, payload⟩ := scope.2
    obtain ⟨foreignRow, foreignFound, foreignPayload⟩ := foreignScope
    obtain ⟨localCut, foreignCut, movedCut, movedToken, cut, moved, captured, _, _, _, _, _⟩ :=
      landing_after_word observe laws respect different separate found payload foreignFound foreignPayload
        landed foreign executed ready origins initial related stamp later (by
          intro child declared token action
          subst token
          exact Reservations.birth landed action (.refl _ _) reservations)
    have native := native_word_of_run foreign foreignFound foreignPayload ready origins executed
    exact ⟨movedCut.1, .last moved (matches_after_foreign native.keeps related.2 captured matched)⟩
  | next landed matched replied rest ih =>
    obtain ⟨row, found, payload⟩ := scope.2
    obtain ⟨foreignRow, foreignFound, foreignPayload⟩ := foreignScope
    obtain ⟨localCut, foreignCut, movedCut, movedToken, rflCut, moved, captured, sameReply, pushed, self, aligned, keptReady⟩ :=
      landing_after_word observe laws respect different separate found payload foreignFound foreignPayload
        landed foreign executed ready origins initial related stamp later (by
          intro child declared token action
          subst token
          exact Reservations.birth landed action rest.keeps reservations)
    have native := native_word_of_run foreign foreignFound foreignPayload ready origins executed
    have newMatch := matches_after_foreign native.keeps related.2 captured matched
    have movedReply := (chosen_reply_at landed matched).trans replied
    have newReply := (chosen_reply_at moved newMatch).symm.trans (sameReply.symm.trans movedReply)
    obtain ⟨actual, actualNative, selects⟩ := landed.reply
    have same := Option.some.inj (actualNative.symm.trans movedReply)
    cases same
    obtain ⟨localTable, localStamps⟩ := localCut
    change localTable = _ at rflCut
    subst localTable
    have frame := ScopedRollback.Keeps.land landed
    obtain ⟨retainedForeign, retainedFound, retainedPayload, _, _⟩ :=
      frame.row foreignActor foreignRow foreignFound
    obtain ⟨last, continued⟩ := ih (successor grammar ⟨_, selects⟩) (frame.compatible scope)
      ⟨retainedForeign, retainedFound, retainedPayload.trans foreignPayload⟩
      localStamps keptReady self pushed aligned (reservations.tail frame)
    exact ⟨last, .next moved newMatch newReply continued⟩

omit [DecidableEq Name] [DecidableEq Key] in
private theorem above_retirements (word : List (Control Name Key Code)) :
    ∃ stamp, ∀ child earlier, Control.retire child earlier ∈ word → earlier < stamp := by
  induction word with
  | nil => exact ⟨0, by simp⟩
  | cons first rest ih =>
    obtain ⟨bound, below⟩ := ih
    cases first with
    | birth parent child declared stamp =>
      refine ⟨bound, ?_⟩
      intro name earlier member
      exact below name earlier ((List.mem_cons.mp member).resolve_left Control.noConfusion)
    | retire child stamp =>
      refine ⟨max (stamp + 1) bound, ?_⟩
      intro name earlier member
      rcases List.mem_cons.mp member with same | remains
      · have age : earlier = stamp := (Control.retire.inj same).2
        omega
      · have age := below name earlier remains
        omega

/-- A successful foreign word preserves admission of the original
compiled calculation once its reservations include the full selected
prefix. The new calculation has the original success or failure status. -/
theorem admitted_after_chosen_word (observe : ∀ key, Setoid (V key))
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, PaperObservationEquations.OperationRespects ops key (observe key).r)
    (lawful : OperationsLawful ops observe)
    (different : actor ≠ foreignActor) (separate : Transposition.Separated component foreignComponent)
    {history : List (Outcome Name ops)} {first final : R} {finished : Bool}
    (chosen : ChosenRun program actor choices history code first final finished)
    (grammar : Mediated program component code)
    (scope : CompatibleProvision.Compatible ops actor component first)
    (foreignScope : ∃ row, first foreignActor = some row ∧ row.component = foreignComponent)
    {foreign : List (Letter program foreignActor)} {replies : List (Reply Name ops Code)}
    {live : Name → Option Nat} {foreignAfter : SR}
    (path : NativePath program foreignActor foreign (first, live) foreignAfter replies)
    (origins : ∀ letter ∈ foreign, letter.origin_has foreignComponent)
    (initial : StampedRelated ops observe (first, live) (first, live))
    (reservations : Reservations first final (controlPart (words foreign))) :
    let plan := admit (actor := actor) choices lawful grammar history
    ∃ (input : plan.domain foreignAfter.1) (moved : R),
      plan.iterator.execute ⟨foreignAfter.1, input⟩ = (if finished then some moved else none) := by
  obtain ⟨foreignRow, foreignFound, foreignPayload⟩ := foreignScope
  have ready := path.ready foreignFound
  have executed := path.record
  have allowed := script_admitted foreign foreignFound foreignPayload ready origins
  have self := PairwiseMixed.mixed_respects ops observe laws (words foreign) allowed initial
  rw [executed] at self
  have native := native_word_of_run foreign foreignFound foreignPayload ready origins executed
  -- These stamps compare hypothetical landings used to check admission.
  -- The original saved retirements retain their own recorded stamps.
  obtain ⟨stamp, later⟩ := above_retirements (controlPart (words foreign))
  obtain ⟨moved, selected⟩ := chosen_after_word observe laws respect different separate foreign origins stamp later
    chosen grammar scope ⟨foreignRow, foreignFound, foreignPayload⟩ live ready initial executed self reservations
  obtain ⟨admitted, returned⟩ := admits_native_run selected grammar lawful (native.keeps.compatible scope)
  exact ⟨admitted, moved, returned⟩

section Generators
variable {observe : ∀ key, Setoid (V key)}
variable (choices : Choices ops Name Code) (lawful : OperationsLawful ops observe)
local notation "N" => Node program actor observe (Interface component)
local notation "compiled" => fun {current : Code} (grammar : Mediated program component current) history =>
  (Node.compiled (recipe (actor := actor) choices lawful grammar history) : N)

/-- The source of a native saved inverse belongs to the acting component
of the canonical iterator. This follows from the original admitted
capture, even if its replay probe has since changed. -/
theorem generator_origin {rootCode : Code} {grammar : Mediated program component rootCode}
    {history : List (Outcome Name ops)} {letter : Letter program actor}
    (generator : Generator (compiled grammar history) letter) : letter.origin_has component := by
  cases generator with
  | advance => exact True.intro
  | replay node reached input result called saved origin output code next agrees drawn =>
    obtain ⟨current, remaining, past, rfl⟩ := reached.mediated choices lawful grammar history
    obtain ⟨row, found, payload⟩ := (mediated_scope choices lawful remaining past input.property).2
    exact ⟨row, origin.symm ▸ found, payload⟩

theorem word_origins {rootCode : Code} {grammar : Mediated program component rootCode}
    {history : List (Outcome Name ops)} {script : List (Letter program actor)}
    (word : Word (compiled grammar history) script) :
    ∀ letter ∈ script, Letter.origin_has letter component := by
  induction word with
  | nil => simp
  | cons head _ ih =>
    intro letter member
    rcases List.mem_cons.mp member with rfl | later
    · exact generator_origin choices lawful head
    · exact ih letter later

/-- The forward generator uses all births in its actual selected
calculation. A replay generator retains existing declarations and adds
no reservation of its own. -/
def GeneratorReservations {root : N} {letter : Letter program actor} (generator : Generator root letter)
    (probe : R) (foreign : List (Control Name Key Code)) : Prop :=
  match generator with
  | .advance node .. =>
    ∃ (current : Code) (grammar : Mediated program component current) (history : List (Outcome Name ops)),
      node = compiled grammar history ∧
      ∃ final finished, ChosenRun program actor choices history current probe final finished ∧
        Reservations probe final foreign
  | .replay .. => True

/-- An admitted generator supplies the retained owner of its edit and
vacancy of any selected birth, even if an ordinary partial call fails. -/
theorem generator_slots {rootCode : Code} {grammar : Mediated program component rootCode}
    {history : List (Outcome Name ops)} {letter : Letter program actor}
    (generator : Generator (compiled grammar history) letter) {state : R}
    (admitted : generator.scope state) (ready : letter.ready state)
    {foreign : List (Control Name Key Code)}
    (reservations : GeneratorReservations choices lawful generator state foreign) :
    PairwiseRegistry.OwnersPresent state (ordinaryPart letter.word) ∧
      ∀ parent child payload stamp, Control.birth parent child payload stamp ∈ controlPart letter.word →
        state child = none := by
  cases generator with
  | advance node reached head drawn =>
    obtain ⟨current, remaining, past, rfl, final, finished, chosen, _⟩ := reservations
    cases head with
    | unit => simp [PairwiseRegistry.OwnersPresent, Letter.word, Forward.word, ordinaryPart, controlPart]
    | provide key value action =>
      obtain ⟨row, found, _⟩ := ready
      simp [PairwiseRegistry.OwnersPresent, Letter.word, Forward.word, ordinaryPart, controlPart, Edit.slot, found]
    | operate owner key name argument action =>
      have route : bindingOwner state actor key = some owner := ready
      have retained : state owner ≠ none := by
        rcases chosen.first with failure | ⟨middle, token, next, landed, _, _⟩
        · cases failure with
          | provide instructed _ => cases action.symm.trans instructed
          | operate oldRoute instructed _ provider name _ =>
            cases action.symm.trans instructed
            have same := Option.some.inj (route.symm.trans name)
            obtain ⟨row, found, _⟩ := provider
            rw [same, found]
            exact Option.noConfusion
        · cases landed with
          | operate _ _ _ used usedName usedArg actual before after inverse reply instructed located _ =>
            cases action.symm.trans instructed
            obtain ⟨boundRoute, binding⟩ := bound_by_location located
            have same := Option.some.inj (route.symm.trans boundRoute)
            intro absent
            rw [← same] at binding
            simp [tableAt, absent] at binding
          | unit _ _ _ instructed | provide _ _ _ _ _ _ instructed _ _ _
            | instantiate _ _ _ _ _ instructed _ => cases action.symm.trans instructed
      simp [PairwiseRegistry.OwnersPresent, Letter.word, Forward.word, ordinaryPart, controlPart, Edit.slot, retained]
    | birth child payload stamp action =>
      have vacant : state child = none := by
        rcases chosen.first with failure | ⟨middle, token, next, landed, matched, _⟩
        · cases failure with
          | provide instructed _ => cases action.symm.trans instructed
          | operate _ instructed _ _ _ _ => cases action.symm.trans instructed
        · have named : capturedChild token = some child :=
            (chosen_landing_draw choices lawful remaining past landed matched).trans drawn.symm
          cases landed with
          | instantiate _ _ _ actual newborn instructed enabled =>
            have same : newborn = child := Option.some.inj named
            exact same ▸ enabled.1
          | unit _ _ _ instructed | provide _ _ _ _ _ _ instructed _ _ _
            | operate _ _ _ _ _ _ _ _ _ _ _ instructed _ _ => cases action.symm.trans instructed
      simp [PairwiseRegistry.OwnersPresent, Letter.word, Forward.word, ordinaryPart, controlPart]
      intro parent name declared index _ same _ _
      simpa only [same] using vacant
  | replay node reached input result called saved origin output code next agrees drawn =>
    obtain ⟨current, remaining, past, rfl⟩ := reached.mediated choices lawful grammar history
    have landed := saved.landed
    rw [origin, code] at landed
    have scope := (mediated_inverse_scope choices lawful remaining past input.property input.property
      called called landed).2
    cases token : saved.token with
    | unit | retire =>
      simp [PairwiseRegistry.OwnersPresent, Letter.word, Saved.word, token, ordinaryPart, controlPart]
    | restrict owner key | operate owner key =>
      rw [token] at scope
      obtain ⟨_, _, _, contains⟩ := scope
      obtain ⟨row, found, _⟩ := (contains state admitted).2
      simp [PairwiseRegistry.OwnersPresent, Letter.word, Saved.word, token, ordinaryPart, controlPart, Edit.slot, found]

private theorem landing_other_tables {state result : R} {token : Inverse Name V} {next : Option Code}
    (landed : Land program actor code state result token next) (covered : Declared program component code)
    (key : Key) (outside : ¬ Interface component key) :
    ∀ owner, tableAt result owner key = tableAt state owner key := by
  cases landed with
  | unit => exact fun _ => rfl
  | provide _ _ _ _ used value action _ _ _ =>
    have declared : Provided component used := by simpa only [Declared, action] using covered
    exact fun owner => tableAt_write_other_key _ _ owner used key
      (fun equal => outside (.inr (equal ▸ declared))) _
  | operate _ _ _ used _ _ _ _ _ _ _ action _ _ =>
    have access : Interface component used := by simpa only [Declared, action] using covered
    exact fun owner => tableAt_write_other_key _ _ owner used key
      (fun equal => outside (equal ▸ access)) _
  | instantiate _ _ _ child nextName _ ready =>
    exact fun owner => congrFun (tablesOf_birth _ nextName child _ ready.1) (owner, key)

private theorem saved_self_related (lawful : OperationsLawful ops observe)
    {code : Code} {state output : R} {token : Inverse Name V} {next : Option Code}
    (landed : Land program actor code state output token next) :
    PairwiseForward.CaptureRelated observe token token := by
  cases landed with
  | unit => exact .unit
  | provide _ _ _ _ key _ _ _ _ _ => exact .restrict actor key
  | operate _ _ _ key name argument owner before after inverse outcome _ _ called =>
    have witness := (lawful key name argument).respect before before ((observe key).refl before)
    rw [called] at witness
    exact .operate owner key witness.2.1
  | instantiate _ _ _ _ name _ _ => exact .retire name

omit [DecidableEq Name] [DecidableEq Key] in
private theorem observed_from_projections {domain : R → Prop}
    {first second : Option SR} {left right : Option (ScopedEffects.State domain)}
    (firstTables : first.map (fun state => tablesOf state.1) = left.map (fun state => tablesOf state.val))
    (secondTables : second.map (fun state => tablesOf state.1) = right.map (fun state => tablesOf state.val))
    (compared : OptionRel (ScopedEffects.Observed observe (fun _ => True)) left right) :
    OptionRel (fun a b : SR => TypedStateObservation.TablesRelatedAt observe (fun _ => True) a.1 b.1) first second := by
  cases first <;> cases second <;> cases left <;> cases right <;>
    simp_all only [Option.map_none, Option.map_some, Option.some.injEq, reduceCtorEq, OptionRel]
  exact AllocationDomains.tables_transfer observe (fun _ => True)
    (fun owner key => congrFun firstTables (owner, key)) (fun owner key => congrFun secondTables (owner, key)) compared

/-- A fixed generator respects table-only observation at two admitted
probes, including its partial failure. The generated word retains its
own provider, draw and inverse choices at both probes. -/
theorem generator_respects_tables {rootCode : Code} {grammar : Mediated program component rootCode}
    {history : List (Outcome Name ops)} {letter : Letter program actor}
    (generator : Generator (compiled grammar history) letter) (first second : SR)
    (left : generator.scope first.1) (right : generator.scope second.1)
    (leftReady : letter.ready first.1) (rightReady : letter.ready second.1)
    (observed : TypedStateObservation.TablesRelatedAt observe (fun _ => True) first.1 second.1) :
    OptionRel (fun a b : SR => TypedStateObservation.TablesRelatedAt observe (fun _ => True) a.1 b.1)
      (runMixed letter.word first) (runMixed letter.word second) := by
  cases generator with
  | advance node reached head drawn =>
    obtain ⟨current, remaining, past, rfl⟩ := reached.mediated choices lawful grammar history
    let node := compiled remaining past
    let a : ScopedEffects.State node.domain := ⟨first.1, left⟩
    let b : ScopedEffects.State node.domain := ⟨second.1, right⟩
    have compared := related_unfold (self_related node) a b (fun key _ => observed key trivial)
    change OptionRel _ (runMixed head.word (a.val, first.2)) (runMixed head.word (b.val, second.2))
    rw [forward_application node head drawn a leftReady first.2, forward_application node head drawn b rightReady second.2]
    cases firstCall : node.evaluate a <;> cases secondCall : node.evaluate b <;>
      simp only [firstCall, secondCall, Option.map_none, Option.map_some, OptionRel] at compared ⊢
    rename_i leftResult rightResult
    obtain ⟨_, leftLand, _⟩ := node.evaluate_native a leftResult firstCall
    obtain ⟨_, rightLand, _⟩ := node.evaluate_native b rightResult secondCall
    intro key _
    by_cases used : Interface component key
    · exact compared.1 key used
    · have unchangedLeft := landing_other_tables leftLand (declared remaining) key used
      have unchangedRight := landing_other_tables rightLand (declared remaining) key used
      simpa only [unchangedLeft, unchangedRight] using observed key trivial
  | replay node reached input result called saved origin output code next agrees drawn =>
    obtain ⟨current, remaining, past, rfl⟩ := reached.mediated choices lawful grammar history
    have landed := saved.landed
    rw [origin, code] at landed
    have scope := (mediated_inverse_scope choices lawful remaining past input.property input.property called called landed).2
    let a : ScopedEffects.State result.domain := ⟨first.1, left⟩
    let b : ScopedEffects.State result.domain := ⟨second.1, right⟩
    have compared := inverse_observation_on_tables agrees agrees (saved_self_related lawful landed) rfl
      (scope.mono (fun _ _ => trivial : ∀ key, Interface component key → (fun _ => True) key)) a b observed
    exact observed_from_projections (saved_application saved result agrees a first.2)
      (saved_application saved result agrees b second.2) compared

/-- On two admitted inputs, a whole compiled generated word respects the
table observation at every executable prefix, including failure. -/
theorem word_respects_tables {rootCode : Code} {grammar : Mediated program component rootCode}
    {history : List (Outcome Name ops)} {script : List (Letter program actor)}
    (word : Word (compiled grammar history) script) {first second : SR}
    (left : word.Admitted first) (right : word.Admitted second)
    (observed : TypedStateObservation.TablesRelatedAt observe (fun _ => True) first.1 second.1) :
    OptionRel (fun a b : SR => TypedStateObservation.TablesRelatedAt observe (fun _ => True) a.1 b.1)
      (word.run first) (word.run second) := by
  rw [word.run_eq left, word.run_eq right]
  induction word generalizing first second with
  | nil => exact observed
  | @cons letter script head tail ih =>
    have heads := generator_respects_tables choices lawful head first second left.1 right.1
      left.2.1 right.2.1 observed
    change OptionRel _ (runMixed (letter.word ++ words script) first) (runMixed (letter.word ++ words script) second)
    rw [split_word, split_word]
    cases firstCall : runMixed letter.word first <;> cases secondCall : runMixed letter.word second <;>
      simp only [firstCall, secondCall, OptionRel, Option.bind_none, Option.bind_some] at heads ⊢
    exact ih (left.2.2 _ firstCall) (right.2.2 _ secondCall) heads

/-- Move a generator's probe scope at a paired cut. Forward calls use the
recovered native continuation. Saved inverses use the retained output
domain of the actual yield. -/
theorem generator_scope_after_word
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, PaperObservationEquations.OperationRespects ops key (observe key).r)
    (different : actor ≠ foreignActor) (separate : Transposition.Separated component foreignComponent)
    {rootCode : Code} {grammar : Mediated program component rootCode} {history : List (Outcome Name ops)}
    {letter : Letter program actor} (generator : Generator (compiled grammar history) letter)
    {first foreignAfter alternate : SR}
    (foreignScope : ∃ row, first.1 foreignActor = some row ∧ row.component = foreignComponent)
    (foreign : List (Letter program foreignActor))
    (ready : ∀ letter ∈ foreign, letter.ready first.1)
    (origins : ∀ letter ∈ foreign, letter.origin_has foreignComponent)
    (initial : StampedRelated ops observe first first)
    (executed : runMixed (words foreign) first = some foreignAfter)
    (related : StampedRelated ops observe foreignAfter alternate)
    (admitted : generator.scope first.1)
    (reservations : GeneratorReservations choices lawful generator first.1 (controlPart (words foreign))) :
    generator.scope alternate.1 := by
  obtain ⟨foreignRow, foreignFound, foreignPayload⟩ := foreignScope
  have native := native_word_of_run foreign foreignFound foreignPayload ready origins executed
  have kept := native.keeps.trans (PairwisePrograms.related_keeps related.2)
  cases generator with
  | advance node reached head drawn =>
    obtain ⟨current, remaining, past, rfl, final, finished, chosen, reservations⟩ := reservations
    have original := mediated_scope choices lawful remaining past admitted
    obtain ⟨stamp, later⟩ := above_retirements (controlPart (words foreign))
    obtain ⟨moved, selected⟩ := chosen_after_word observe laws respect different separate foreign origins stamp later
      chosen remaining original ⟨foreignRow, foreignFound, foreignPayload⟩ first.2 ready initial executed related reservations
    exact (admits_native_run selected remaining lawful (kept.compatible original)).1
  | replay node reached input result called saved origin output code next agrees drawn =>
    obtain ⟨current, remaining, past, rfl⟩ := reached.mediated choices lawful grammar history
    exact mediated_inverse_frame choices lawful remaining past input called kept admitted

/-- A moved yield compares the whole continuation, its saved partial
function on compatible admitted probes, and the component of an actual
child in both outputs. -/
def YieldPreserved (left right : Yield program actor observe (Interface component)) : Prop :=
  left.reply = right.reply ∧ left.next = right.next ∧
    (∀ p : ScopedEffects.State left.domain, ∀ q : ScopedEffects.State right.domain,
      ScopedEffects.Observed observe (Interface component) p q →
        OptionRel (ScopedEffects.Observed observe (Interface component)) (left.inverse p) (right.inverse q)) ∧
    ∀ child, left.reply = .child child → ∃ payload,
      left.output.val child = some (fresh payload (some actor)) ∧
        right.output.val child = some (fresh payload (some actor))

/-- The foreign-word clause for every reachable compiled head, including
genuine head failure. Reservation checks use the actual selected
calculation at the original admitted probe. -/
theorem generator_yield_after_word
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, PaperObservationEquations.OperationRespects ops key (observe key).r)
    (different : actor ≠ foreignActor) (separate : Transposition.Separated component foreignComponent)
    {rootCode : Code} {grammar : Mediated program component rootCode} {history : List (Outcome Name ops)}
    {node : N} (reached : Reach (compiled grammar history) node)
    (head : Forward program actor node.code) (drawn : head.draw = node.draw)
    {first foreignAfter alternate : SR}
    (foreignScope : ∃ row, first.1 foreignActor = some row ∧ row.component = foreignComponent)
    (foreign : List (Letter program foreignActor))
    (ready : ∀ letter ∈ foreign, letter.ready first.1)
    (origins : ∀ letter ∈ foreign, letter.origin_has foreignComponent)
    (initial : StampedRelated ops observe first first)
    (executed : runMixed (words foreign) first = some foreignAfter)
    (related : StampedRelated ops observe foreignAfter alternate)
    (admitted : node.domain first.1) (headReady : head.ready first.1)
    (reservations : GeneratorReservations choices lawful (.advance node reached head drawn)
      first.1 (controlPart (words foreign))) :
    ∃ moved : node.domain alternate.1,
      OptionRel YieldPreserved (node.evaluate ⟨first.1, admitted⟩) (node.evaluate ⟨alternate.1, moved⟩) := by
  have moved := generator_scope_after_word choices lawful laws respect different separate
    (.advance node reached head drawn) foreignScope foreign ready origins initial executed related admitted reservations
  refine ⟨moved, ?_⟩
  obtain ⟨current, remaining, past, rfl, final, finished, chosen, preserves⟩ := reservations
  have scope := mediated_scope choices lawful remaining past admitted
  obtain ⟨actorRow, actorFound, payload⟩ := scope.2
  obtain ⟨foreignRow, foreignFound, foreignPayload⟩ := foreignScope
  have nativeWord := native_word_of_run foreign foreignFound foreignPayload ready origins executed
  rcases chosen.first with failure | ⟨middle, token, next, landed, matched, suffix⟩
  · have movedFailure := failure_after_related observe respect related.2
      (failure_after_foreign observe laws different separate remaining scope failure nativeWord)
    have failed {probe : R} (scope : (compiled remaining past).domain probe)
        (native : ChosenFailure program actor choices current probe) :
        (compiled remaining past).evaluate ⟨probe, scope⟩ = none := by
      cases called : (compiled remaining past).evaluate ⟨probe, scope⟩ with
      | none => rfl
      | some result =>
        obtain ⟨_, landed, _⟩ := (compiled remaining past).evaluate_native ⟨probe, scope⟩ result called
        exact False.elim (native.no_landing landed)
    rw [failed admitted failure, failed moved movedFailure]
    exact True.intro
  · have named : capturedChild token = head.draw :=
      (chosen_landing_draw choices lawful remaining past landed matched).trans drawn.symm
    obtain ⟨_, foreignToken, movedLand, foreignCapture, foreignReply⟩ :=
      rerun_after_native_word observe laws actorFound different (by simpa only [payload] using separate)
        landed nativeWord (by
          intro child declared captured action other row vacant present
          obtain ⟨parent, stamp, born⟩ := runMixed_birth_of_new_row executed vacant present
          subst token
          exact Reservations.birth landed action suffix preserves parent other row.component stamp born)
    obtain ⟨last, movedToken, transported, _, movedCapture, movedReply⟩ :=
      PairwisePrograms.transport_landing observe program respect related.2 movedLand
    have captures := foreignCapture.symm.trans movedCapture
    have sameDraw : capturedChild movedToken = head.draw := by
      cases captures <;> exact named
    obtain ⟨reply, replied, _⟩ := landed.reply
    have left : (Letter.advance current head).Native first (middle, head.stamps first.2) (.advance token next reply) :=
      ⟨landed, named, rfl, headReady, by rw [← named]; exact replied⟩
    have right : (Letter.advance current head).Native alternate (last, head.stamps alternate.2)
        (.advance movedToken next reply) :=
      ⟨transported, sameDraw, rfl, (Letter.advance current head).ready_related related.2
        (head.ready_after_word headReady executed), by
          rw [← sameDraw, ← movedReply, ← foreignReply]
          exact replied⟩
    have paired : Reply.Related observe (.advance token next reply) (.advance movedToken next reply) :=
      ⟨rfl, captures, rfl⟩
    obtain ⟨a, b, firstEq, secondEq, firstOutput, secondOutput, recorded, sameReply, sameNext, leftInverse, rightInverse⟩ :=
      reify_paired_heads (compiled remaining past) head drawn ⟨first.1, admitted⟩ ⟨alternate.1, moved⟩ left right paired
    obtain ⟨sameScope, slotScope⟩ := mediated_inverse_scope choices lawful remaining past admitted moved firstEq secondEq landed
    rw [firstEq, secondEq]
    refine ⟨sameReply, sameNext,
      fun p q observed => inverse_observation_on_tables leftInverse rightInverse captures sameScope slotScope p q observed, ?_⟩
    intro child childReply
    have same : reply = .child child := recorded.symm.trans childReply
    rw [same] at left right paired
    obtain ⟨component, _, born, otherBorn⟩ := paired_child_payload (compiled remaining past) head left right paired
    rw [firstOutput, secondOutput]
    exact ⟨component, born, otherBorn⟩

/-- Check reservations at each executable prefix of the original
generator word. A forward check includes its selected continuation. -/
def WordReservations {root : N} : {script : List (Letter program actor)} →
    Word root script → SR → List (Control Name Key Code) → Prop
  | [], .nil, _, _ => True
  | letter :: _, .cons head tail, before, foreign =>
    GeneratorReservations choices lawful head before.1 foreign ∧
      ∀ middle, runMixed letter.word before = some middle → WordReservations tail middle foreign

/-- The reservations of the selected full calculations imply the
reservations of the births actually executed by the generated word. -/
theorem word_birth_reservations {root : N} {script : List (Letter program actor)}
    (word : Word root script) {before after : SR} {replies : List (Reply Name ops Code)}
    (path : NativePath program actor script before after replies)
    {foreign : List (Control Name Key Code)}
    (reservations : WordReservations choices lawful word before foreign) :
    ∀ child declared stamp, Control.birth actor child declared stamp ∈ controlPart (words script) →
      ∀ parent other payload earlier, Control.birth parent other payload earlier ∈ foreign →
        DrawCompatible child other declared payload := by
  induction word generalizing before after replies with
  | nil => simp [words, controlPart]
  | @cons letter tail head word ih =>
    cases path with
    | @cons _ _ _ middle _ reply replies native rest =>
      obtain ⟨headReservations, tailReservations⟩ := reservations
      intro child declared stamp inScript parent other payload earlier foreignBirth
      change Control.birth actor child declared stamp ∈ controlPart (letter.word ++ words tail) at inScript
      rw [controlPart, List.filterMap_append, ← controlPart, ← controlPart] at inScript
      rcases List.mem_append.mp inScript with inHead | inTail
      · cases head with
        | replay node reached input yielded called saved origin output code next agrees drawn =>
          cases token : saved.token <;> simp [Letter.word, Saved.word, token, controlPart] at inHead
        | advance node reached head drawn =>
          cases head with
          | unit | provide | operate => simp [Letter.word, Forward.word, controlPart] at inHead
          | birth newborn childComponent birthStamp action =>
            have same : child = newborn ∧ declared = childComponent ∧ stamp = birthStamp := by
              simpa [Letter.word, Forward.word, controlPart] using inHead
            obtain ⟨rfl, rfl, rfl⟩ := same
            obtain ⟨code, remaining, history, rfl, final, finished, chosen, reserves⟩ := headReservations
            cases reply with
            | replay => exact False.elim native
            | advance captured continuation outcome =>
              obtain ⟨landed, named, _, _, _⟩ := native
              rcases chosen.first with failure | ⟨finish, token, next, actual, matched, keeps⟩
              · exact False.elim (failure.no_landing landed)
              have chosenName := chosen_landing_draw choices lawful remaining history actual matched
              have equal := named.trans (drawn.trans chosenName.symm)
              obtain ⟨_, tokenEq, _⟩ := typed_landing_deterministic landed actual equal
              have retiring : token = .retire child := by
                rw [← tokenEq]
                cases captured <;> simp [capturedChild, Forward.draw] at named ⊢
                exact named
              rw [retiring] at actual
              exact Reservations.birth actual action keeps reserves parent other payload earlier foreignBirth
      · exact ih rest (tailReservations middle (letter.record_native native)) child declared stamp inTail
          parent other payload earlier foreignBirth

/-- Derive admission at every executable reordered prefix and retain an
original partial failure. Each successful moved application has a
corresponding foreign execution at the original next prefix. -/
theorem word_scope_after_foreign
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, PaperObservationEquations.OperationRespects ops key (observe key).r)
    (different : actor ≠ foreignActor) (separate : Transposition.Separated component foreignComponent)
    {rootCode : Code} {grammar : Mediated program component rootCode} {history : List (Outcome Name ops)}
    {script : List (Letter program actor)} (word : Word (compiled grammar history) script)
    (foreign : List (Letter program foreignActor))
    (origins : ∀ letter ∈ foreign, letter.origin_has foreignComponent)
    (births : ∀ edit ∈ controlPart (words script), ∀ other ∈ controlPart (words foreign),
      PairwiseControl.Compatible edit other)
    {first foreignAfter alternate : SR}
    (localScope : ∃ row, first.1 actor = some row ∧ row.component = component)
    (foreignScope : ∃ row, first.1 foreignActor = some row ∧ row.component = foreignComponent)
    (ready : ∀ letter ∈ foreign, letter.ready first.1)
    (initial : StampedRelated ops observe first first)
    (executed : runMixed (words foreign) first = some foreignAfter)
    (related : StampedRelated ops observe foreignAfter alternate)
    (admitted : word.Admitted first)
    (reservations : WordReservations choices lawful word first (controlPart (words foreign))) :
    word.Admitted alternate ∧
      (runMixed (words script) first = none → runMixed (words script) alternate = none) := by
  induction word generalizing first foreignAfter alternate with
  | nil => exact ⟨trivial, fun impossible => False.elim (Option.noConfusion impossible)⟩
  | @cons letter script head tail ih =>
    obtain ⟨headScope, headReady, tailScope⟩ := admitted
    obtain ⟨headReservations, tailReservations⟩ := reservations
    obtain ⟨row, found, payload⟩ := localScope
    obtain ⟨foreignRow, foreignFound, foreignPayload⟩ := foreignScope
    have headControls (edit) (member : edit ∈ controlPart letter.word) := births edit (by
      change edit ∈ controlPart (letter.word ++ words script)
      simpa only [controlPart, List.filterMap_append] using List.mem_append_left _ member)
    have tailControls (edit) (member : edit ∈ controlPart (words script)) := births edit (by
      change edit ∈ controlPart (letter.word ++ words script)
      simpa only [controlPart, List.filterMap_append] using List.mem_append_right _ member)
    have allowed := letter.admitted found payload headReady (generator_origin choices lawful head)
    have foreignAllowed := script_admitted foreign foreignFound foreignPayload ready origins
    obtain ⟨headOwners, headVacancy⟩ := generator_slots choices lawful head headScope headReady headReservations
    have foreignOwners := PairwiseMixed.mixed_owners_present ops (words foreign)
      (by rw [foreignFound]; exact Option.noConfusion) foreignAllowed executed
    have joint : PairwiseMixed.Scoped (letter.word ++ words foreign) := by
      apply PairwiseMixed.scoped_of_vacant_births _ first.1
      · intro edit member
        have sides : edit ∈ ordinaryPart letter.word ++ ordinaryPart (words foreign) := by
          simpa only [ordinaryPart, List.filterMap_append] using member
        exact (List.mem_append.mp sides).elim (headOwners edit) (foreignOwners edit)
      · intro parent child declared stamp member
        have sides : Control.birth parent child declared stamp ∈ controlPart letter.word ++ controlPart (words foreign) := by
          simpa only [controlPart, List.filterMap_append] using member
        exact (List.mem_append.mp sides).elim (headVacancy parent child declared stamp)
          (PairwiseMixed.birth_vacant_at_source _ executed parent child declared stamp)
    have continueAt {movedMiddle : SR} (movedHead : runMixed letter.word alternate = some movedMiddle) :
        ∃ middle, runMixed letter.word first = some middle ∧ tail.Admitted movedMiddle ∧
          (runMixed (words script) middle = none → runMixed (words script) movedMiddle = none) := by
      have pairedHead := PairwiseMixed.mixed_respects ops observe laws letter.word allowed related
      rw [movedHead] at pairedHead
      cases foreignHead : runMixed letter.word foreignAfter with
      | none => simp [foreignHead, OptionRel] at pairedHead
      | some foreignMiddle =>
        rw [foreignHead] at pairedHead
        have compare := PairwiseMixed.mixed_words_commute ops observe laws different separate
          first letter.word (words foreign) allowed foreignAllowed headOwners foreignOwners joint headControls initial.2
        rw [split_word, split_word, executed] at compare
        change OptionRel _ (runMixed letter.word foreignAfter)
          ((runMixed letter.word first).bind (runMixed (words foreign))) at compare
        rw [foreignHead] at compare
        cases firstHead : runMixed letter.word first with
        | none => simp [firstHead, OptionRel] at compare
        | some middle =>
          rw [firstHead, Option.bind_some] at compare
          cases pushed : runMixed (words foreign) middle with
          | none => simp [pushed, OptionRel] at compare
          | some newForeign =>
            rw [pushed] at compare
            have matched : StampedRelated ops observe newForeign movedMiddle :=
              ⟨compare.1.symm.trans pairedHead.1, compare.2.symm.trans pairedHead.2⟩
            have self := PairwiseMixed.mixed_respects ops observe laws letter.word allowed initial
            rw [firstHead] at self
            obtain ⟨nextRow, nextFound, nextPayload, _⟩ := runMixed_keeps_row firstHead found
            obtain ⟨nextForeign, nextForeignFound, nextForeignPayload, _⟩ := runMixed_keeps_row firstHead foreignFound
            exact ⟨middle, rfl, ih tailControls ⟨nextRow, nextFound, nextPayload.trans payload⟩
              ⟨nextForeign, nextForeignFound, nextForeignPayload.trans foreignPayload⟩
              (fun l member => l.ready_after_word (ready l member) firstHead) self pushed matched
              (tailScope middle firstHead) (tailReservations middle firstHead)⟩
    constructor
    · exact ⟨generator_scope_after_word choices lawful laws respect different separate head
        ⟨foreignRow, foreignFound, foreignPayload⟩ foreign ready origins initial executed related headScope headReservations,
        letter.ready_related related.2 (letter.ready_after_word headReady executed),
        fun _ movedHead => (continueAt movedHead).choose_spec.2.1⟩
    · intro fails
      change runMixed (letter.word ++ words script) first = none at fails
      change runMixed (letter.word ++ words script) alternate = none
      rw [split_word]
      cases movedHead : runMixed letter.word alternate with
      | none => rfl
      | some movedMiddle =>
        obtain ⟨middle, firstHead, _, movedTail⟩ := continueAt movedHead
        rw [split_word, firstHead, Option.bind_some] at fails
        exact movedTail fails

/-- An admitted word can be evaluated after the independently
successful foreign path. Any original partial failure is preserved. -/
theorem word_after_native_path
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, PaperObservationEquations.OperationRespects ops key (observe key).r)
    (different : actor ≠ foreignActor) (separate : Transposition.Separated component foreignComponent)
    {rootCode : Code} {grammar : Mediated program component rootCode} {history : List (Outcome Name ops)}
    {script : List (Letter program actor)} (word : Word (compiled grammar history) script)
    {foreign : List (Letter program foreignActor)} {replies : List (Reply Name ops Code)}
    (origins : ∀ letter ∈ foreign, letter.origin_has foreignComponent)
    (births : ∀ edit ∈ controlPart (words script), ∀ other ∈ controlPart (words foreign),
      PairwiseControl.Compatible edit other)
    {first foreignAfter : SR} {foreignRow : Fiber Name V Code}
    (localScope : ∃ row, first.1 actor = some row ∧ row.component = component)
    (foreignFound : first.1 foreignActor = some foreignRow) (foreignPayload : foreignRow.component = foreignComponent)
    (initial : StampedRelated ops observe first first)
    (native : NativePath program foreignActor foreign first foreignAfter replies)
    (admitted : word.Admitted first)
    (reservations : WordReservations choices lawful word first (controlPart (words foreign))) :
    word.Admitted foreignAfter ∧ (word.run first = none → word.run foreignAfter = none) := by
  have ready := native.ready foreignFound
  have allowed := script_admitted foreign foreignFound foreignPayload ready origins
  have paired := PairwiseMixed.mixed_respects ops observe laws (words foreign) allowed initial
  rw [native.record] at paired
  obtain ⟨movedScope, movesFailure⟩ := word_scope_after_foreign choices lawful laws respect different separate word
    foreign origins births localScope ⟨foreignRow, foreignFound, foreignPayload⟩ ready initial native.record paired
    admitted reservations
  refine ⟨movedScope, ?_⟩
  intro failed
  rw [word.run_eq admitted] at failed
  rw [word.run_eq movedScope, movesFailure failed]

end Generators

/-- The two compiled generated words compare their complete partial
compositions. Their successful original runs, selected reservation
checks, and cross-birth compatibility derive all reordered scopes. -/
theorem compiled_words_commute (observe : ∀ key, Setoid (V key))
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, PaperObservationEquations.OperationRespects ops key (observe key).r)
    (lawful : OperationsLawful ops observe)
    {leftActor rightActor : Name} {leftComponent rightComponent : Calculus.Component Key Code}
    {leftCode rightCode : Code}
    (leftGrammar : Mediated program leftComponent leftCode) (rightGrammar : Mediated program rightComponent rightCode)
    (leftChoices rightChoices : Choices ops Name Code) (leftHistory rightHistory : List (Outcome Name ops))
    {leftScript : List (Letter program leftActor)} {rightScript : List (Letter program rightActor)}
    (leftWord : Word (Node.compiled (recipe (actor := leftActor) leftChoices lawful leftGrammar leftHistory)) leftScript)
    (rightWord : Word (Node.compiled (recipe (actor := rightActor) rightChoices lawful rightGrammar rightHistory)) rightScript)
    {first leftEnd rightEnd : SR} {leftRow rightRow : Fiber Name V Code}
    (different : leftActor ≠ rightActor) (separate : Transposition.Separated leftComponent rightComponent)
    (leftFound : first.1 leftActor = some leftRow) (leftPayload : leftRow.component = leftComponent)
    (rightFound : first.1 rightActor = some rightRow) (rightPayload : rightRow.component = rightComponent)
    (leftRun : leftWord.run first = some leftEnd) (rightRun : rightWord.run first = some rightEnd)
    (births : ∀ edit ∈ controlPart (words leftScript), ∀ other ∈ controlPart (words rightScript),
      PairwiseControl.Compatible edit other)
    (leftReservations : WordReservations leftChoices lawful leftWord first (controlPart (words rightScript)))
    (rightReservations : WordReservations rightChoices lawful rightWord first (controlPart (words leftScript)))
    (initial : StampedRelated ops observe first first) :
    OptionRel (StampedRelated ops observe) (leftWord.run rightEnd) (rightWord.run leftEnd) := by
  obtain ⟨leftAdmitted, _, leftPath⟩ := leftWord.run_iff.mp leftRun
  obtain ⟨rightAdmitted, _, rightPath⟩ := rightWord.run_iff.mp rightRun
  have leftOrigins := word_origins leftChoices lawful leftWord
  have rightOrigins := word_origins rightChoices lawful rightWord
  have leftReady := leftPath.ready leftFound
  have rightReady := rightPath.ready rightFound
  have leftAllowed := script_admitted leftScript leftFound leftPayload leftReady leftOrigins
  have rightAllowed := script_admitted rightScript rightFound rightPayload rightReady rightOrigins
  have leftSelf := PairwiseMixed.mixed_respects ops observe laws (words leftScript) leftAllowed initial
  have rightSelf := PairwiseMixed.mixed_respects ops observe laws (words rightScript) rightAllowed initial
  rw [leftPath.record] at leftSelf
  rw [rightPath.record] at rightSelf
  have leftMoved := word_scope_after_foreign leftChoices lawful laws respect different separate leftWord
    rightScript rightOrigins births ⟨leftRow, leftFound, leftPayload⟩ ⟨rightRow, rightFound, rightPayload⟩
    rightReady initial rightPath.record rightSelf leftAdmitted leftReservations
  have rightMoved := word_scope_after_foreign rightChoices lawful laws respect different.symm separate.symm rightWord
    leftScript leftOrigins (fun other rightMem edit leftMem => (births edit leftMem other rightMem).symm)
    ⟨rightRow, rightFound, rightPayload⟩ ⟨leftRow, leftFound, leftPayload⟩
    leftReady initial leftPath.record leftSelf rightAdmitted rightReservations
  exact Word.commute_on_scopes observe laws leftWord rightWord different
    (by simpa only [leftPayload, rightPayload] using separate) leftFound rightFound
    (by simpa only [leftPayload] using leftOrigins) (by simpa only [rightPayload] using rightOrigins)
    leftRun rightRun leftMoved.1 rightMoved.1 births initial.2

/-- Full partial-map commutation at a common admitted probe. The option
comparison includes either original word failing, both failing, and
failure at any stage of either reordered composition. -/
theorem compiled_partial_words_commute (observe : ∀ key, Setoid (V key))
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, PaperObservationEquations.OperationRespects ops key (observe key).r)
    (lawful : OperationsLawful ops observe)
    {leftActor rightActor : Name} {leftComponent rightComponent : Calculus.Component Key Code}
    {leftCode rightCode : Code}
    (leftGrammar : Mediated program leftComponent leftCode) (rightGrammar : Mediated program rightComponent rightCode)
    (leftChoices rightChoices : Choices ops Name Code) (leftHistory rightHistory : List (Outcome Name ops))
    {leftScript : List (Letter program leftActor)} {rightScript : List (Letter program rightActor)}
    (leftWord : Word (Node.compiled (recipe (actor := leftActor) leftChoices lawful leftGrammar leftHistory)) leftScript)
    (rightWord : Word (Node.compiled (recipe (actor := rightActor) rightChoices lawful rightGrammar rightHistory)) rightScript)
    {first : SR} {leftRow rightRow : Fiber Name V Code}
    (different : leftActor ≠ rightActor) (separate : Transposition.Separated leftComponent rightComponent)
    (leftFound : first.1 leftActor = some leftRow) (leftPayload : leftRow.component = leftComponent)
    (rightFound : first.1 rightActor = some rightRow) (rightPayload : rightRow.component = rightComponent)
    (leftAdmitted : leftWord.Admitted first) (rightAdmitted : rightWord.Admitted first)
    (births : ∀ edit ∈ controlPart (words leftScript), ∀ other ∈ controlPart (words rightScript),
      PairwiseControl.Compatible edit other)
    (leftReservations : WordReservations leftChoices lawful leftWord first (controlPart (words rightScript)))
    (rightReservations : WordReservations rightChoices lawful rightWord first (controlPart (words leftScript)))
    (initial : StampedRelated ops observe first first) :
    OptionRel (StampedRelated ops observe) ((rightWord.run first).bind leftWord.run)
      ((leftWord.run first).bind rightWord.run) := by
  cases leftRun : leftWord.run first <;> cases rightRun : rightWord.run first
  · exact True.intro
  · rename_i rightEnd
    obtain ⟨_, _, path⟩ := rightWord.run_iff.mp rightRun
    have moved := word_after_native_path leftChoices lawful laws respect different separate leftWord
      (word_origins rightChoices lawful rightWord) births ⟨leftRow, leftFound, leftPayload⟩ rightFound rightPayload
      initial path leftAdmitted leftReservations
    have failed := moved.2 leftRun
    simp only [Option.bind_some, Option.bind_none, failed, OptionRel]
  · rename_i leftEnd
    obtain ⟨_, _, path⟩ := leftWord.run_iff.mp leftRun
    have moved := word_after_native_path rightChoices lawful laws respect different.symm separate.symm rightWord
      (word_origins leftChoices lawful leftWord) (fun other rm edit lm => (births edit lm other rm).symm)
      ⟨rightRow, rightFound, rightPayload⟩ leftFound leftPayload initial path rightAdmitted rightReservations
    have failed := moved.2 rightRun
    simp only [Option.bind_none, Option.bind_some, failed, OptionRel]
  · exact compiled_words_commute observe laws respect lawful leftGrammar rightGrammar
      leftChoices rightChoices leftHistory rightHistory leftWord rightWord different separate
      leftFound leftPayload rightFound rightPayload leftRun rightRun births leftReservations rightReservations initial

/-- Each saved retirement in a word comes from a capture recorded at the
common cut or a birth at its own name and stamp earlier in the word. -/
def RetirementSources (captures : List (IncarnationReplay.Capture Name Key (Scalar ops)))
    (script : List (Letter program actor)) : Prop :=
  ∀ earlier saved later, script = earlier ++ .replay saved :: later →
    ∀ child, saved.token = .retire child →
      IncarnationReplay.Capture.mk (encodeInverse ops saved.token) saved.stamp ∈ captures ∨
        ∃ payload, Control.birth actor child payload saved.stamp ∈ controlPart (words earlier)

theorem retirement_chronology {last cut : Nat} (trace : GuardedHistory.Trace (encodeProgram program) last)
    (bounded : cut ≤ last) {script : List (Letter program actor)}
    (sources : RetirementSources ((trace.notes cut).2 actor) script) :
    ∀ child stamp, Control.retire child stamp ∈ controlPart (words script) →
      stamp ≤ cut ∨ ∃ payload, Control.birth actor child payload stamp ∈ controlPart (words script) := by
  intro child stamp member
  obtain ⟨edit, inWord, picked⟩ := List.mem_filterMap.mp member
  obtain ⟨letter, inScript, inLetter⟩ := List.mem_flatMap.mp inWord
  cases letter with
  | advance current head =>
    cases head <;> simp_all [Letter.word, Forward.word]
  | replay saved =>
    obtain ⟨earlier, later, split⟩ := List.append_of_mem inScript
    cases actual : saved.token with
    | unit | restrict | operate => simp_all [Letter.word, Saved.word]
    | retire target =>
      have same : edit = .inl (.retire target saved.stamp) := by simpa [Letter.word, Saved.word, actual] using inLetter
      subst edit
      change some (Control.retire target saved.stamp) = some (.retire child stamp) at picked
      obtain ⟨rfl, rfl⟩ := Control.retire.inj (Option.some.inj picked)
      rcases sources earlier saved later split target actual with recorded | ⟨payload, prior⟩
      · exact .inl (trace.capture_origin cut bounded actor _ recorded).1
      · refine .inr ⟨payload, ?_⟩
        rw [split]
        simp only [words, List.flatMap_append, controlPart, List.filterMap_append]
        exact List.mem_append_left _ prior

/-- At an actual guarded cut, the two original generated words need only
compare their child reservations. Recorded captures precede later births.
A capture produced within a word cannot target the other word's child
because the selected names are distinct. -/
theorem compiled_words_commute_at_trace_cut (observe : ∀ key, Setoid (V key))
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, PaperObservationEquations.OperationRespects ops key (observe key).r)
    (lawful : OperationsLawful ops observe)
    {leftActor rightActor : Name} {leftComponent rightComponent : Calculus.Component Key Code}
    {leftCode rightCode : Code}
    (leftGrammar : Mediated program leftComponent leftCode) (rightGrammar : Mediated program rightComponent rightCode)
    (leftChoices rightChoices : Choices ops Name Code) (leftHistory rightHistory : List (Outcome Name ops))
    {leftScript : List (Letter program leftActor)} {rightScript : List (Letter program rightActor)}
    (leftWord : Word (Node.compiled (recipe (actor := leftActor) leftChoices lawful leftGrammar leftHistory)) leftScript)
    (rightWord : Word (Node.compiled (recipe (actor := rightActor) rightChoices lawful rightGrammar rightHistory)) rightScript)
    {last cut : Nat} (trace : GuardedHistory.Trace (encodeProgram program) last) (bounded : cut ≤ last)
    {state : R} {leftEnd rightEnd : SR} {leftRow rightRow : Fiber Name V Code}
    (different : leftActor ≠ rightActor) (separate : Transposition.Separated leftComponent rightComponent)
    (leftFound : state leftActor = some leftRow) (leftPayload : leftRow.component = leftComponent)
    (rightFound : state rightActor = some rightRow) (rightPayload : rightRow.component = rightComponent)
    (leftSources : RetirementSources ((trace.notes cut).2 leftActor) leftScript)
    (rightSources : RetirementSources ((trace.notes cut).2 rightActor) rightScript)
    (leftLater : ∀ child declared stamp, Control.birth leftActor child declared stamp ∈ controlPart (words leftScript) → cut < stamp)
    (rightLater : ∀ child declared stamp, Control.birth rightActor child declared stamp ∈ controlPart (words rightScript) → cut < stamp)
    (leftRun : leftWord.run (state, (trace.notes cut).1) = some leftEnd)
    (rightRun : rightWord.run (state, (trace.notes cut).1) = some rightEnd)
    (leftReservations : WordReservations leftChoices lawful leftWord (state, (trace.notes cut).1) (controlPart (words rightScript)))
    (rightReservations : WordReservations rightChoices lawful rightWord (state, (trace.notes cut).1) (controlPart (words leftScript)))
    (initial : PairwisePrograms.Related (ops := ops) observe state state) :
    OptionRel (StampedRelated ops observe) (leftWord.run rightEnd) (rightWord.run leftEnd) := by
  obtain ⟨_, _, leftPath⟩ := leftWord.run_iff.mp leftRun
  obtain ⟨_, _, rightPath⟩ := rightWord.run_iff.mp rightRun
  have reservations := word_birth_reservations leftChoices lawful leftWord leftPath leftReservations
  have births := control_compatibility_at_cut leftScript rightScript
    (by change state leftActor ≠ none; rw [leftFound]; exact Option.noConfusion)
    (by change state rightActor ≠ none; rw [rightFound]; exact Option.noConfusion)
    leftPath.record rightPath.record cut leftLater rightLater
    (retirement_chronology trace bounded leftSources) (retirement_chronology trace bounded rightSources)
    (fun left declared lStamp lBorn right payload rStamp rBorn =>
      reservations left declared lStamp lBorn rightActor right payload rStamp rBorn)
  exact compiled_words_commute observe laws respect lawful leftGrammar rightGrammar
    leftChoices rightChoices leftHistory rightHistory leftWord rightWord different separate
    leftFound leftPayload rightFound rightPayload leftRun rightRun births leftReservations rightReservations ⟨rfl, initial⟩

end Cordis.Repairs.ScopedAdmissionExchange
