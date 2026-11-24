import Cordis.Repairs.PairwiseForward
import Cordis.Repairs.ScopedProgram

/-! Complete native calculations across the related probes produced by
primitive exchanges. The paired path retains every selected code, original
draw and component payload, and compares actual partial captures. -/
namespace Cordis.Repairs.PairwisePrograms
open TypedRegistry
open PaperEffectEquations (CoeffectOperations ValueOperationWitness)
open PaperObservationEquations (OperationRespects)
open PartialCoeffectIndependenceContracts (tableSetoid)
open PairwiseForward (CaptureRelated AllowsPair forward_square_at_probe)
open ScopedProgram (Landings)
open Iterators (OptionRel)

universe u
variable {Name Key Code : Type u} {V : Key → Type u} [DecidableEq Name] [DecidableEq Key]
variable {ops : CoeffectOperations V}
local notation "R" => Registry Name V Code
local notation "I" => Inverse Name V
local notation "Program" => Code → Instruction Name ops Code

abbrev Related (observe : ∀ key, Setoid (V key)) (left right : R) : Prop :=
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  StageSimulation.Related Eq (encodeRegistry ops left) (encodeRegistry ops right)

theorem Related.symm {observe : ∀ key, Setoid (V key)} {left right : R}
    (related : Related (ops := ops) observe left right) : Related (ops := ops) observe right left := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  exact StageSimulation.Related.symm (fun _ _ equal => equal.symm) related

theorem Related.trans {observe : ∀ key, Setoid (V key)} {left middle right : R}
    (first : Related (ops := ops) observe left middle) (second : Related (ops := ops) observe middle right) :
    Related (ops := ops) observe left right := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  exact StageSimulation.Related.trans (Value := Scalar ops) (Q := Eq) (fun a b => a.trans b) first second

/-- Move a native head to an observationally related compatible probe.
The actual typed partial inverse is compared prior to total encoding. -/
theorem transport_landing (observe : ∀ key, Setoid (V key)) (program : Program)
    (respect : ∀ key, OperationRespects ops key (observe key).r)
    {actor : Name} {code : Code} {before alternate after : R} {saved : I} {next : Option Code}
    (sources : Related (ops := ops) observe before alternate)
    (native : Land program actor code before after saved next) :
    ∃ moved inverse, Land program actor code alternate moved inverse next ∧
      Related (ops := ops) observe after moved ∧ CaptureRelated observe saved inverse ∧
      replyAt program actor (capturedChild saved) code before =
        replyAt program actor (capturedChild inverse) code alternate := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  cases native with
  | unit _ _ _ action => exact ⟨_, .unit, .unit _ _ _ action, sources, .unit, by simp [replyAt, action]⟩
  | provide _ _ _ row key value action found provided vacant =>
    have rawFound : encodeRegistry ops before actor = some (encodeFiber ops row) := by
      simp [encodeRegistry, found]
    obtain ⟨otherRow, rawOther, fields⟩ := StageSimulation.present_related sources actor _ rawFound
    obtain ⟨typedRow, typedFound, rfl⟩ := encodeRegistry_some ops rawOther
    have providing : row.component.provides = typedRow.component.provides := fields.component.provides
    have declared : typedRow.component.provides key = true := by simpa only [← providing] using provided
    have absent : typedRow.table key = none := by
      have rawAbsent : (encodeFiber ops row).table key = none := by simp [encodeFiber, vacant]
      exact Option.map_eq_none_iff.mp ((GuardObservations.table_none_iff fields.observed key).mp rawAbsent)
    refine ⟨_, .restrict actor key, .provide _ _ _ _ _ _ action typedFound declared absent, ?_, .restrict actor key,
      by simp [replyAt, action]⟩
    change StageSimulation.Related Eq (encodeRegistry ops (write before actor key (some value))) _
    simp only [encode_write, Option.map_some]
    exact StageSimulation.write_related sources actor key (Setoid.refl _)
  | operate _ _ _ key name arg owner input output inverse result action located called =>
    have rawLocated : Stages.location (encodeRegistry ops before) actor key =
        some (owner, TypedCoeffectReplay.pack key input) := by
      rw [encode_location, located]
      rfl
    obtain ⟨rawInput, rawOther, rawRelated⟩ := GuardObservations.location_success sources.observed actor owner key _ rawLocated
    rw [encode_location] at rawOther
    obtain ⟨⟨otherOwner, otherInput⟩, otherLocated, same⟩ := Option.map_eq_some_iff.mp rawOther
    have ownerEq : otherOwner = owner := congrArg Prod.fst same
    have inputEq : TypedCoeffectReplay.pack key otherInput = rawInput := congrArg Prod.snd same
    subst otherOwner rawInput
    have inputs : (observe key).r input otherInput :=
      (TypedCoeffectReplay.packed_related (Yield := Yield ops) observe key _ _).mp rawRelated
    have calls := respect key name arg input otherInput inputs
    rw [called] at calls
    cases moved : (ops.operation key name arg).run otherInput with
    | none => simp [moved, OptionRel] at calls
    | some reply =>
      obtain ⟨otherOutput, otherInverse, otherResult⟩ := reply
      rw [moved] at calls
      obtain ⟨outputs, captured, sameResult⟩ := calls
      change result = otherResult at sameResult
      subst otherResult
      refine ⟨_, .operate owner key otherInverse, .operate _ _ _ _ _ _ _ _ _ _ _ action otherLocated moved, ?_,
        .operate owner key captured, by simp [replyAt, action, located, otherLocated, called, moved]⟩
      change StageSimulation.Related Eq (encodeRegistry ops (write before owner key (some output))) _
      simp only [encode_write, Option.map_some]
      apply StageSimulation.write_related sources owner key
      exact (TypedCoeffectReplay.packed_related (Yield := Yield ops) observe key _ _).mpr outputs
  | instantiate _ _ _ component child action ready =>
    have fields : StageSimulation.ComponentRelated Eq component component := ⟨rfl, rfl, rfl⟩
    have rawReady := (insertable_encode_iff ops before child component (some actor)).mpr ready
    have pairedReady := (insertable_encode_iff ops alternate child component (some actor)).mp
      (StageSimulation.insertable_related sources child fields (some actor) rawReady)
    refine ⟨_, .retire child, .instantiate _ _ _ _ _ action pairedReady, ?_, .retire child, by simp [replyAt, action]⟩
    change StageSimulation.Related Eq (encodeRegistry ops (put before child (fresh component (some actor)))) _
    simp only [encode_put, encode_fresh]
    exact StageSimulation.put_related sources child (StageSimulation.fresh_related fields (some actor))

/-- Two complete native calculations with the same outcome-selected code
at each stage. The stage records both captures and the structural relation
at its resulting cut. -/
inductive PairedLandings (observe : ∀ key, Setoid (V key)) (program : Program) (actor : Name) :
    Code → R → R → R → R → List I → List I → Prop where
  | last {code src other dest otherDest first second} :
    Land program actor code src dest first none → Land program actor code other otherDest second none →
    Related (ops := ops) observe dest otherDest → CaptureRelated observe first second →
    PairedLandings observe program actor code src other dest otherDest [first] [second]
  | next {code following src other middle otherMiddle dest otherDest first second tail otherTail} :
    Land program actor code src middle first (some following) →
    Land program actor code other otherMiddle second (some following) →
    Related (ops := ops) observe middle otherMiddle → CaptureRelated observe first second →
    PairedLandings observe program actor following middle otherMiddle dest otherDest tail otherTail →
    PairedLandings observe program actor code src other dest otherDest (first :: tail) (second :: otherTail)

theorem PairedLandings.toRight {observe : ∀ key, Setoid (V key)} {program : Program} {actor : Name} {code : Code}
    {before alternate after moved : R} {word otherWord : List I}
    (paired : PairedLandings observe program actor code before alternate after moved word otherWord) :
    Landings program actor code alternate moved otherWord := by
  induction paired with
  | last _ landed _ _ => exact .last landed
  | next _ landed _ _ _ ih => exact .next landed ih

theorem PairedLandings.endpoints {observe : ∀ key, Setoid (V key)} {program : Program} {actor : Name} {code : Code}
    {before alternate after moved : R} {word otherWord : List I}
    (paired : PairedLandings observe program actor code before alternate after moved word otherWord) :
    Related (ops := ops) observe after moved := by
  induction paired with
  | last _ _ observed _ => exact observed
  | next _ _ _ _ _ ih => exact ih

/-- Transport all stages of an arbitrary successful mixed calculation. No
new continuation, owner or fresh-name choice is supplied by the target probe. -/
theorem transport_landings (observe : ∀ key, Setoid (V key)) (program : Program)
    (respect : ∀ key, OperationRespects ops key (observe key).r)
    {actor : Name} {code : Code} {before alternate after : R} {word : List I}
    (sources : Related (ops := ops) observe before alternate)
    (native : Landings program actor code before after word) :
    ∃ moved otherWord, PairedLandings observe program actor code before alternate after moved word otherWord := by
  induction native generalizing alternate with
  | last head =>
    obtain ⟨moved, capture, paired, observed, related, _⟩ := transport_landing observe program respect sources head
    exact ⟨moved, [capture], .last head paired observed related⟩
  | next head _ ih =>
    obtain ⟨middle, capture, paired, observed, related, _⟩ := transport_landing observe program respect sources head
    obtain ⟨moved, otherWord, rest⟩ := ih observed
    exact ⟨moved, capture :: otherWord, .next head paired observed related rest⟩

inductive CaptureWordRelated (observe : ∀ key, Setoid (V key)) : List I → List I → Prop where
  | nil : CaptureWordRelated observe [] []
  | cons {a b as bs} : CaptureRelated observe a b → CaptureWordRelated observe as bs →
    CaptureWordRelated observe (a :: as) (b :: bs)

omit [DecidableEq Name] [DecidableEq Key] in
theorem CaptureWordRelated.symm (observe : ∀ key, Setoid (V key)) {left right : List I}
    (related : CaptureWordRelated observe left right) : CaptureWordRelated observe right left := by
  induction related with
  | nil => exact .nil
  | cons head _ ih => exact .cons head.symm ih

omit [DecidableEq Name] [DecidableEq Key] in
theorem CaptureWordRelated.trans {observe : ∀ key, Setoid (V key)} {left middle right : List I}
    (first : CaptureWordRelated observe left middle) (second : CaptureWordRelated observe middle right) :
    CaptureWordRelated observe left right := by
  induction first generalizing right with
  | nil => cases second; exact .nil
  | cons head _ ih =>
    cases second with
    | cons other tail => exact .cons (head.trans other) (ih tail)

theorem PairedLandings.captures {observe : ∀ key, Setoid (V key)} {program : Program} {actor : Name} {code : Code}
    {before alternate after moved : R} {word otherWord : List I}
    (paired : PairedLandings observe program actor code before alternate after moved word otherWord) :
    CaptureWordRelated observe word otherWord := by
  induction paired with
  | last _ _ _ captured => exact .cons captured .nil
  | next _ _ _ captured _ ih => exact .cons captured ih

private theorem landing_keeps_component {program : Program} {actor name : Name} {code : Code}
    {before after : R} {row : Fiber Name V Code} {token : I} {next : Option Code}
    (landed : Land program actor code before after token next) (found : before name = some row) :
    ∃ current, after name = some current ∧ current.component = row.component := by
  have source : encodeRegistry ops before name = some (encodeFiber ops row) := by simp [encodeRegistry, found]
  obtain ⟨entry, raw, same, _⟩ := Ordering.land_existing_control (encodeProgram program)
    (land_encode ops landed) name _ source
  obtain ⟨current, typed, encoded⟩ := encodeRegistry_some ops raw
  rw [← encoded] at same
  exact ⟨current, typed, same⟩

private theorem landings_keep_component {program : Program} {actor name : Name} {code : Code}
    {before after : R} {row : Fiber Name V Code} {word : List I}
    (landed : Landings program actor code before after word) (found : before name = some row) :
    ∃ current, after name = some current ∧ current.component = row.component := by
  induction landed generalizing row with
  | last head => exact landing_keeps_component head found
  | next head _ ih =>
    obtain ⟨middle, present, same⟩ := landing_keeps_component head found
    obtain ⟨entry, ready, component⟩ := ih present
    exact ⟨entry, ready, component.trans same⟩

/-- Check a selected foreign birth against every actual child of a native
calculation. The final registry gives their real component payloads because
primitive landings preserve existing rows and declarations. -/
def AllowsWord (program : Program) (foreignCode : Code) (foreignToken : I) (after : R) (word : List I) : Prop :=
  ∀ foreignChild payload, foreignToken = .retire foreignChild → (program foreignCode).action = .instantiate payload →
    ∀ child row, Inverse.retire child ∈ word → after child = some row →
      PairwiseAllocation.DrawCompatible child foreignChild row.component payload

private theorem allows_head {program : Program} {actor : Name} {code foreignCode : Code}
    {before middle after : R} {token foreignToken : I} {next : Option Code} {word : List I}
    (head : Land program actor code before middle token next)
    (keeps : ∀ name row, middle name = some row → ∃ current, after name = some current ∧ current.component = row.component)
    (allowed : AllowsWord program foreignCode foreignToken after (token :: word)) :
    AllowsPair program code foreignCode token foreignToken := by
  cases head with
  | unit => exact True.intro
  | provide => exact True.intro
  | operate => exact True.intro
  | instantiate _ _ _ component child action _ =>
    cases foreignToken <;> try exact True.intro
    rename_i otherChild
    cases foreignAction : (program foreignCode).action <;> simp [AllowsPair, action, foreignAction]
    rename_i payload
    have installed : put before child (fresh component (some actor)) child = some (fresh component (some actor)) := by
      simp [put]
    obtain ⟨row, found, same⟩ := keeps child _ installed
    simpa only [same] using allowed otherChild payload rfl foreignAction child row List.mem_cons_self found

omit [DecidableEq Name] [DecidableEq Key] in
private theorem allows_tail {observe : ∀ key, Setoid (V key)} {program : Program} {foreignCode : Code}
    {foreignToken movedToken head : I} {after : R} {tail : List I}
    (allowed : AllowsWord program foreignCode foreignToken after (head :: tail))
    (token : CaptureRelated observe movedToken foreignToken) : AllowsWord program foreignCode movedToken after tail := by
  intro child payload captured action nextChild row member found
  exact allowed child payload (token.symm.retirement captured) action nextChild row
    (List.mem_cons_of_mem _ member) found

/-- Move one foreign primitive across a complete native calculation. The
original selected branches and child payloads are followed at each square.
The proof transports the remainder at the related intermediate cuts and
preserves both words' actual partial captures. -/
theorem forward_through_landings (observe : ∀ key, Setoid (V key)) (program : Program)
    (respect : ∀ key, OperationRespects ops key (observe key).r)
    (recovery : ValueOperationWitness ops)
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    {first second : Name} (different : first ≠ second) {firstCode : Code} {before after : R} {word : List I}
    (localWord : Landings program first firstCode before after word) :
    ∀ {foreignCode : Code} {beforeLocal : R} {foreignToken : I} {foreignNext : Option Code}
      {firstRow secondRow : Fiber Name V Code},
      before first = some firstRow → before second = some secondRow →
      Transposition.Separated firstRow.component secondRow.component →
      WellFormed.Disjoint (encodeRegistry ops before) → Related (ops := ops) observe before before →
      Land program second foreignCode before beforeLocal foreignToken foreignNext →
      AllowsWord program foreignCode foreignToken after word →
      ∃ afterLocal afterForeign movedWord movedToken,
        Landings program first firstCode beforeLocal afterLocal movedWord ∧
        Land program second foreignCode after afterForeign movedToken foreignNext ∧
        CaptureWordRelated observe movedWord word ∧ CaptureRelated observe movedToken foreignToken ∧
        Related (ops := ops) observe afterLocal afterForeign := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  induction localWord with
  | last head =>
    intro foreignCode beforeLocal foreignToken foreignNext firstRow secondRow firstFound secondFound separate disjoint self foreign allowed
    have compatible := allows_head head (fun _ row found => ⟨row, found, rfl⟩) allowed
    obtain ⟨afterForeign, afterLocal, localInverse, foreignInverse, movedForeign, movedLocal, lc, fc, endpoints⟩ :=
      forward_square_at_probe observe program firstFound secondFound different separate disjoint recovery laws
        head foreign compatible self
    exact ⟨afterLocal, afterForeign, [localInverse], foreignInverse, .last movedLocal, movedForeign, .cons lc .nil, fc, endpoints⟩
  | next head tail ih =>
    intro foreignCode beforeLocal foreignToken foreignNext firstRow secondRow firstFound secondFound separate disjoint self foreign allowed
    have compatible := allows_head head (fun _ _ found => landings_keep_component tail found) allowed
    obtain ⟨headThenForeign, foreignThenHead, newHead, newForeign, movedForeign, movedHead, lc, fc, endpoints⟩ :=
      forward_square_at_probe observe program firstFound secondFound different separate disjoint recovery laws
        head foreign compatible self
    obtain ⟨localEntry, stillFirst, sameFirst⟩ := landing_keeps_component head firstFound
    obtain ⟨foreignEntry, stillSecond, sameSecond⟩ := landing_keeps_component head secondFound
    have separateTail : Transposition.Separated localEntry.component foreignEntry.component := by
      simpa only [sameFirst, sameSecond] using separate
    have disjointTail := WellFormed.land_disjoint _ (land_encode ops head) disjoint
    have selfTail := Transposition.landing_self_related _ (land_encode ops head) self
    obtain ⟨movedTail, endForeign, tailWord, saved, tailAfter, doneForeign, tails, foreignCapture, ends⟩ :=
      ih stillFirst stillSecond separateTail disjointTail selfTail movedForeign (allows_tail allowed fc)
    have aligned := StageSimulation.Related.symm (fun _ _ equal => equal.symm) endpoints
    obtain ⟨endLocal, newTail, paired⟩ := transport_landings observe program respect aligned tailAfter
    refine ⟨endLocal, endForeign, newHead :: newTail, saved, .next movedHead paired.toRight, doneForeign,
      .cons lc ((paired.captures.symm observe).trans tails), foreignCapture.trans fc, ?_⟩
    exact paired.endpoints.symm.trans ends

omit [DecidableEq Name] [DecidableEq Key] in
theorem CaptureWordRelated.retire_mem {observe : ∀ key, Setoid (V key)} {left right : List I}
    (related : CaptureWordRelated observe left right) (child : Name) :
    Inverse.retire child ∈ left ↔ Inverse.retire child ∈ right := by
  induction related with
  | nil => rfl
  | cons head _ ih =>
    constructor
    · intro member
      rcases List.mem_cons.mp member with eq | tail
      · exact List.mem_cons.mpr (.inl (head.symm.retirement eq.symm).symm)
      · exact List.mem_cons.mpr (.inr (ih.mp tail))
    · intro member
      rcases List.mem_cons.mp member with eq | tail
      · exact List.mem_cons.mpr (.inl (head.retirement eq.symm).symm)
      · exact List.mem_cons.mpr (.inr (ih.mpr tail))

private theorem birth_present {program : Program} {actor child : Name} {code : Code}
    {before after : R} {next : Option Code} (landed : Land program actor code before after (.retire child) next) :
    ∃ component, (program code).action = .instantiate component ∧ after child = some (fresh component (some actor)) := by
  cases landed with
  | instantiate _ _ _ payload _ action _ => exact ⟨payload, action, by simp [put]⟩

private theorem landings_birth_present {program : Program} {actor : Name} {code : Code}
    {before after : R} {word : List I} (path : Landings program actor code before after word) (child : Name)
    (member : Inverse.retire child ∈ word) : ∃ row, after child = some row := by
  induction path with
  | last head =>
    have same := List.mem_singleton.mp member
    subst same
    obtain ⟨payload, _, birth⟩ := birth_present head
    exact ⟨_, birth⟩
  | next head tail ih =>
    rcases List.mem_cons.mp member with same | rest
    · subst same
      obtain ⟨payload, _, born⟩ := birth_present head
      obtain ⟨row, found, _⟩ := landings_keep_component tail born
      exact ⟨row, found⟩
    · exact ih rest

theorem related_component {observe : ∀ key, Setoid (V key)} {before after : R}
    {name : Name} {row : Fiber Name V Code} (related : Related (ops := ops) observe before after)
    (found : before name = some row) : ∃ other, after name = some other ∧ other.component = row.component := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  have rawFound : encodeRegistry ops before name = some (encodeFiber ops row) := by simp [encodeRegistry, found]
  obtain ⟨encoded, rawOther, fields⟩ := StageSimulation.present_related related name _ rawFound
  obtain ⟨other, present, rfl⟩ := encodeRegistry_some ops rawOther
  have declarations : row.component = other.component := by
    exact Calculus.Component.mk.injEq .. |>.mpr ⟨fields.component.requires, fields.component.provides, fields.component.entry⟩
  exact ⟨other, present, declarations.symm⟩

theorem related_bindingOwner {observe : ∀ key, Setoid (V key)} {before after : R}
    (related : Related (ops := ops) observe before after) (actor : Name) (key : Key) :
    bindingOwner before actor key = bindingOwner after actor key := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  simpa only [encode_bindingOwner] using GuardObservations.bindingOwner_related related.observed actor key

/-- Related native registries retain the structural compiled scope,
including finite rootedness and the retained committed provider routes. -/
theorem related_keeps {observe : ∀ key, Setoid (V key)} {before after : R}
    (related : Related (ops := ops) observe before after) : ScopedRollback.Keeps ops before after := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  have raw := related.observed
  have backward := GuardObservations.related_symm raw
  constructor
  · rintro ⟨⟨closed, rank, ranked⟩, ⟨names, finite⟩, owned, disjoint⟩
    refine ⟨⟨?_, rank, ?_⟩, ⟨names, ?_⟩, ?_, ?_⟩
    · intro child row parent present hasParent
      obtain ⟨old, found, fields⟩ := GuardObservations.present_related backward child row present
      intro absent
      exact closed child old parent found (fields.parent.symm.trans hasParent)
        ((GuardObservations.none_iff raw parent).mpr absent)
    · intro child row parent present hasParent
      obtain ⟨old, found, fields⟩ := GuardObservations.present_related backward child row present
      exact ranked child old parent found (fields.parent.symm.trans hasParent)
    · intro name row present
      obtain ⟨old, found, _⟩ := GuardObservations.present_related backward name row present
      exact finite name old found
    · intro name row key present bound
      obtain ⟨old, found, fields⟩ := GuardObservations.present_related backward name row present
      rw [fields.provides]
      exact owned name old key found (fun vacant => bound ((GuardObservations.table_none_iff fields key).mpr vacant))
    · intro first second row other firstFound secondFound distinct key shared
      obtain ⟨old, oldAt, fields⟩ := GuardObservations.present_related backward first row firstFound
      obtain ⟨prior, priorAt, otherFields⟩ := GuardObservations.present_related backward second other secondFound
      exact disjoint first second old prior oldAt priorAt distinct key
        ⟨(congrFun fields.provides key).symm.trans shared.1, (congrFun otherFields.provides key).symm.trans shared.2⟩
  · intro name row found
    obtain ⟨other, otherAt, component⟩ := related_component related found
    have first := encode_row (ops := ops) found
    have second := encode_row (ops := ops) otherAt
    obtain ⟨paired, pairedAt, fields⟩ := GuardObservations.present_related raw name _ first
    cases Option.some.inj (pairedAt.symm.trans second)
    exact ⟨other, otherAt, component, fields.parent.symm,
      by simpa only [encodeFiber, encodePhase_committed] using fields.committed.symm⟩

/-- All actual child reservations of either original calculation may coexist
with those of the other. Existing allocations are already checked by each
native calculation. This condition compares only the two sets of new births. -/
def AllowsWords (left right : R) (leftWord rightWord : List I) : Prop :=
  ∀ child otherChild row otherRow, Inverse.retire child ∈ leftWord → Inverse.retire otherChild ∈ rightWord →
    left child = some row → right otherChild = some otherRow →
    PairwiseAllocation.DrawCompatible child otherChild row.component otherRow.component

private theorem allows_word_of_head {program : Program} {actor : Name} {code : Code}
    {before middle after left : R} {token : I} {next : Option Code} {leftWord rightWord : List I}
    (landed : Land program actor code before middle token next) (member : token ∈ rightWord)
    (keeps : ∀ name row, middle name = some row → ∃ other, after name = some other ∧ other.component = row.component)
    (allowed : AllowsWords left after leftWord rightWord) : AllowsWord program code token left leftWord := by
  intro otherChild payload tokenEq action child row localMember localFound
  subst token
  obtain ⟨component, label, present⟩ := birth_present landed
  obtain ⟨otherRow, found, same⟩ := keeps otherChild _ present
  have payloadEq := Action.instantiate.inj (label.symm.trans action)
  subst payload
  simpa only [same] using allowed child otherChild row otherRow localMember member localFound found

/-- Two complete native calculations can execute in either order under
the actual cross-birth check and the separated interfaces. Every primitive's
partial inverse stays paired with its counterpart, including the exact
child captured at each allocating stage. -/
theorem forward_words_square (observe : ∀ key, Setoid (V key)) (program : Program)
    (respect : ∀ key, OperationRespects ops key (observe key).r)
    (recovery : ValueOperationWitness ops)
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    {first second : Name} (different : first ≠ second) {secondCode : Code} {before right : R} {rightWord : List I}
    (rightPath : Landings program second secondCode before right rightWord) :
    ∀ {firstCode : Code} {left : R} {leftWord : List I} {firstRow secondRow : Fiber Name V Code},
      before first = some firstRow → before second = some secondRow →
      Transposition.Separated firstRow.component secondRow.component →
      WellFormed.Disjoint (encodeRegistry ops before) → Related (ops := ops) observe before before →
      Landings program first firstCode before left leftWord → AllowsWords left right leftWord rightWord →
      ∃ afterLeft afterRight movedLeft movedRight,
        Landings program second secondCode left afterLeft movedRight ∧
        Landings program first firstCode right afterRight movedLeft ∧
        CaptureWordRelated observe movedLeft leftWord ∧ CaptureWordRelated observe movedRight rightWord ∧
        Related (ops := ops) observe afterRight afterLeft := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  induction rightPath with
  | last head =>
    intro firstCode left leftWord firstRow secondRow leftFound rightFound separate disjoint self leftPath compatible
    have allowed := allows_word_of_head head (by simp) (fun _ row found => ⟨row, found, rfl⟩) compatible
    obtain ⟨afterRight, afterLeft, newLeft, newRight, movedLeft, movedRight, leftCaptures, rightCapture, endpoints⟩ :=
      forward_through_landings observe program respect recovery laws different leftPath
        leftFound rightFound separate disjoint self head allowed
    exact ⟨afterLeft, afterRight, newLeft, [newRight], .last movedRight, movedLeft, leftCaptures, .cons rightCapture .nil, endpoints⟩
  | next head tail ih =>
    intro firstCode left leftWord firstRow secondRow leftFound rightFound separate disjoint self leftPath compatible
    rename_i finish token tokens
    have allowed := allows_word_of_head head List.mem_cons_self (fun _ _ found => landings_keep_component tail found) compatible
    obtain ⟨headThenLeft, leftThenHead, newLeft, newHead, movedLeft, movedHead, leftCaptures, headCapture, endpoints⟩ :=
      forward_through_landings observe program respect recovery laws different leftPath
        leftFound rightFound separate disjoint self head allowed
    obtain ⟨localEntry, stillFirst, sameFirst⟩ := landing_keeps_component head leftFound
    obtain ⟨foreignEntry, stillSecond, sameSecond⟩ := landing_keeps_component head rightFound
    have tailSeparate : Transposition.Separated localEntry.component foreignEntry.component := by
      simpa only [sameFirst, sameSecond] using separate
    have tailDisjoint := WellFormed.land_disjoint _ (land_encode ops head) disjoint
    have tailSelf := Transposition.landing_self_related _ (land_encode ops head) self
    have tailAllowed : AllowsWords headThenLeft finish newLeft tokens := by
      intro child otherChild row otherRow memLeft memTail foundLeft foundRight
      have oldMember := (leftCaptures.retire_mem child).mp memLeft
      obtain ⟨oldRow, oldFound⟩ := landings_birth_present leftPath child oldMember
      obtain ⟨afterHead, afterHeadFound, agreesHead⟩ := landing_keeps_component movedHead oldFound
      obtain ⟨matched, matchedFound, agreesMoved⟩ := related_component endpoints.symm afterHeadFound
      have same := Option.some.inj (matchedFound.symm.trans foundLeft)
      subst row
      simpa only [agreesMoved, agreesHead] using compatible child otherChild oldRow otherRow oldMember
        (List.mem_cons_of_mem _ memTail) oldFound foundRight
    obtain ⟨afterTail, afterRight, lastLeft, newTail, movedTail, finalLeft, finalCaptures, tailCaptures, compared⟩ :=
      ih stillFirst stillSecond tailSeparate tailDisjoint tailSelf movedLeft tailAllowed
    obtain ⟨afterLeft, lastTail, paired⟩ := transport_landings observe program respect endpoints movedTail
    exact ⟨afterLeft, afterRight, lastLeft, newHead :: lastTail, .next movedHead paired.toRight, finalLeft,
      finalCaptures.trans leftCaptures, .cons headCapture ((paired.captures.symm observe).trans tailCaptures),
      compared.trans paired.endpoints⟩

/-- At a reachable common cut, both complete orders retain each original
birth's component in both endpoints. The native run supplies disjointness
and the source's relation to itself. -/
theorem forward_words_at_reachable (observe : ∀ key, Setoid (V key)) (program : Program)
    (respect : ∀ key, OperationRespects ops key (observe key).r)
    (recovery : ValueOperationWitness ops)
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    {first second : Name} (different : first ≠ second) {firstCode secondCode : Code}
    {before left right : R} {leftWord rightWord : List I} {firstRow secondRow : Fiber Name V Code}
    (firstFound : before first = some firstRow) (secondFound : before second = some secondRow)
    (separate : Transposition.Separated firstRow.component secondRow.component)
    (reached : WellFormed.Run (encodeProgram program) (fun _ => none) (encodeRegistry ops before))
    (leftPath : Landings program first firstCode before left leftWord)
    (rightPath : Landings program second secondCode before right rightWord)
    (compatible : AllowsWords left right leftWord rightWord) :
    ∃ afterLeft afterRight newLeft newRight,
      Landings program second secondCode left afterLeft newRight ∧
      Landings program first firstCode right afterRight newLeft ∧
      CaptureWordRelated observe newLeft leftWord ∧ CaptureWordRelated observe newRight rightWord ∧
      Related (ops := ops) observe afterRight afterLeft ∧
      ∀ child row, (left child = some row ∨ right child = some row) →
        ∃ l r, afterLeft child = some l ∧ afterRight child = some r ∧
          l.component = row.component ∧ r.component = row.component := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  have disjoint := (WellFormed.run_invariants _ reached Safety.empty_parentClosed WellFormed.disjoint_empty
    ⟨Ordering.supported_empty, Ordering.local_empty⟩).2.1
  have self := Transposition.reachable_self_related _ (encoded_program_callbacks ops observe program recovery laws) reached
  obtain ⟨afterLeft, afterRight, newLeft, newRight, movedRight, movedLeft, leftCaptures, rightCaptures, endpoints⟩ :=
    forward_words_square observe program respect recovery laws different rightPath firstFound secondFound separate
      disjoint self leftPath compatible
  refine ⟨afterLeft, afterRight, newLeft, newRight, movedRight, movedLeft, leftCaptures, rightCaptures, endpoints, ?_⟩
  intro child row source
  rcases source with fromLeft | fromRight
  · obtain ⟨l, foundLeft, sameLeft⟩ := landings_keep_component movedRight fromLeft
    obtain ⟨r, foundRight, sameRight⟩ := related_component endpoints.symm foundLeft
    exact ⟨l, r, foundLeft, foundRight, sameLeft, sameRight.trans sameLeft⟩
  · obtain ⟨r, foundRight, sameRight⟩ := landings_keep_component movedLeft fromRight
    obtain ⟨l, foundLeft, sameLeft⟩ := related_component endpoints foundRight
    exact ⟨l, r, foundLeft, foundRight, sameLeft.trans sameRight, sameRight⟩

end Cordis.Repairs.PairwisePrograms
