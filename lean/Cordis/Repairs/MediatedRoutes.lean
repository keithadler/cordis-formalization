import Cordis.Repairs.MediatedAdmission
import Cordis.Repairs.ScopedRollback

/-! Recover the provider and fresh-draw choices for an actual native iterator
calculation. Actor metadata and its committed routes are stable. A foreign
binding at a later stage already had a provider row at the input. -/
namespace Cordis.Repairs.MediatedAdmission
open TypedRegistry ScopedProgram ScopedRollback
open PaperEffectEquations (CoeffectOperations)
universe u
variable {Name Key Code : Type u} {V : Key → Type u}
variable [DecidableEq Name] [DecidableEq Key] {ops : CoeffectOperations V}
local notation "R" => Registry Name V Code
local notation "I" => Inverse Name V
variable {program : Code → Instruction Name ops Code} {actor : Name}
variable {observe : ∀ key, Setoid (V key)}
variable {component : Calculus.Component Key Code} {code : Code}

/-- The committed route and the declaration it selects at the source.
An absent route has no operation probes. -/
def sourceRoute (state : R) (actor : Name) (key : Key) : Option (Route Name Code key) := do
  let owner ← bindingOwner state actor key
  let provider ← state owner
  if supplied : Provided provider.component key then
    some ⟨owner, provider.component, supplied⟩
  else none

private theorem keeps_foreign_bindings {before after : R} {token : I} {next : Option Code}
    (landed : Land program actor code before after token next)
    (owner : Name) (key : Key) (foreign : owner ≠ actor) (bound : tableAt after owner key ≠ none) :
    tableAt before owner key ≠ none := by
  cases landed with
  | unit => exact bound
  | provide =>
    simpa [tableAt, write, TypedRegistry.modify, foreign] using bound
  | operate _ _ _ changed _ _ provider old value _ _ _ located _ =>
    by_cases sameOwner : owner = provider
    · subst owner
      by_cases sameKey : key = changed
      · subst key
        rw [(bound_by_location located).2]
        exact Option.noConfusion
      · cases found : before provider <;>
          simp_all [tableAt, write, TypedRegistry.modify, Ne.symm sameKey]
    · simpa [tableAt, write, TypedRegistry.modify, sameOwner] using bound
  | instantiate _ _ _ childComponent child _ _ =>
    by_cases same : owner = child
    · subst owner
      simp [tableAt, put, fresh] at bound
    · simpa [tableAt, put, same] using bound

private structure FromSource (ops : CoeffectOperations V) (actor : Name) (initial state : R) : Prop where
  keeps : Keeps ops initial state
  foreign : ∀ owner key, owner ≠ actor → tableAt state owner key ≠ none → tableAt initial owner key ≠ none

private theorem FromSource.step {initial before after : R} {token : I} {next : Option Code}
    (frame : FromSource ops actor initial before)
    (landed : Land program actor code before after token next) :
    FromSource ops actor initial after :=
  ⟨frame.keeps.trans (Keeps.land landed), fun owner key foreign bound =>
    frame.foreign owner key foreign (keeps_foreign_bindings landed owner key foreign bound)⟩

omit [DecidableEq Name] in
private theorem provided_of_bound {state : R} (allowed : CompatibleProvision.Allowed ops state)
    {owner : Name} {row : Fiber Name V Code} (found : state owner = some row)
    {key : Key} {value : V key} (bound : tableAt state owner key = some value) :
    Provided row.component key := by
  have source := allowed.2.2.1 owner (encodeFiber ops row) key
  apply source (by simp [encodeRegistry, found])
  have table : row.table key = some value := by simpa [tableAt, found] using bound
  simp [encodeFiber, table]

/-- A provider read by a native landing is the source's committed route,
including the original provider component. No route is assumed for a key
that the calculation has never successfully read. -/
private theorem route_of_call {initial state : R} (context : FromSource ops actor initial state)
    (compatible : CompatibleProvision.Compatible ops actor component initial)
    {owner : Name} {key : Key} {value : V key} (located : location state actor key = some (owner, value)) :
    ∃ route, sourceRoute initial actor key = some route ∧ owner = route.owner ∧
      ∃ provider, state owner = some provider ∧ provider.component = route.provider := by
  obtain ⟨route, bound⟩ := bound_by_location located
  obtain ⟨actorRow, actorAt, _⟩ := compatible.2
  have available : initial owner ≠ none := by
    intro absent
    by_cases same : owner = actor
    · subst owner
      rw [actorAt] at absent
      cases absent
    · have boundAt : tableAt state owner key ≠ none := bound ▸ Option.noConfusion
      exact context.foreign owner key same boundAt (by simp [tableAt, absent])
  cases initialProvider : initial owner with
  | none => exact False.elim (available initialProvider)
  | some provider =>
    obtain ⟨current, entry, declaration, _, _⟩ := context.keeps.row owner provider initialProvider
    have sourceBinding : bindingOwner initial actor key = some owner :=
      (context.keeps.bindingOwner actorAt key).symm.trans route
    have supplied : Provided provider.component key := by
      have observed := provided_of_bound (context.keeps.allowed compatible.1) entry bound
      rwa [declaration] at observed
    refine ⟨⟨owner, provider.component, supplied⟩, ?_, rfl, current, entry, declaration⟩
    simp [sourceRoute, sourceBinding, initialProvider]
    exact supplied

private theorem matches_landing {initial before after : R} {token : I} {next : Option Code}
    (context : FromSource ops actor initial before)
    (compatible : CompatibleProvision.Compatible ops actor component initial)
    (landed : Land program actor code before after token next)
    (choices : Choices ops Name Code) (history : List (Outcome Name ops))
    (routes : choices.route = sourceRoute initial actor)
    (draw : ∀ child, token = .retire child → choices.draw code history = child) :
    Matches choices history code before token := by
  cases landed with
  | unit | provide => trivial
  | operate _ _ _ key _ _ owner value _ _ _ _ located _ =>
    have chosen := route_of_call context compatible located
    simpa only [Matches, routes] using chosen
  | instantiate _ _ _ _ child _ _ => exact draw child rfl

private theorem choose_run {initial before after : R} {tokens : List I}
    (landed : Landings program actor code before after tokens)
    (compatible : CompatibleProvision.Compatible ops actor component initial)
    (context : FromSource ops actor initial before) (choices : Choices ops Name Code)
    (routes : choices.route = sourceRoute initial actor) (history : List (Outcome Name ops))
    (draws : ∀ index child (past : List (Outcome Name ops)) current,
      tokens[index]? = some (.retire child) → past.length = history.length + index →
      choices.draw current past = child) :
    ChosenRun program actor choices history code before after true := by
  induction landed generalizing history with
  | last head =>
    refine .last head (matches_landing context compatible head choices history routes ?_)
    intro child rfl
    exact draws 0 child history _ rfl (by simp)
  | next head tail ih =>
    have matched := matches_landing context compatible head choices history routes (fun child captured => by
      cases captured
      exact draws 0 child history _ rfl (by simp))
    obtain ⟨reply, replied, _⟩ := head.reply
    refine .next head matched ((chosen_reply_at head matched).symm.trans replied)
      (ih (context.step head) (reply :: history) ?_)
    intro index child past current found length
    exact draws (index + 1) child past current (List.getElem?_cons_succ.trans found) (by
      simp only [List.length_cons] at length
      omega)

def choicesOf (ops : CoeffectOperations V) (initial : R) (actor : Name) (tokens : List I) :
    Choices ops Name Code where
  route := sourceRoute initial actor
  draw _ history :=
    match tokens[history.length]? with
    | some (.retire child) => child
    | _ => actor

/-- Recover the choices from the committed source view and the actual saved
tokens. Every subsequent native stage retains its true selected outcome. -/
theorem choose_actual_run {before after : R} {tokens : List I}
    (landed : Landings program actor code before after tokens)
    (compatible : CompatibleProvision.Compatible ops actor component before) :
    ChosenRun program actor (choicesOf ops before actor tokens) [] code before after true := by
  refine choose_run landed compatible
    ⟨Keeps.refl ops before, fun _ _ _ bound => bound⟩ (choicesOf ops before actor tokens) rfl [] ?_
  intro index child past current found length
  simp only [List.length_nil, Nat.zero_add] at length
  simp [choicesOf, length, found]

/-- For any successful native calculation of the mediated grammar, synthesize
its scopes and the continuation links from the actual route and draw choices. -/
theorem admits_actual_run {before after : R} {tokens : List I}
    (landed : Landings program actor code before after tokens)
    (grammar : Mediated program component code) (lawful : OperationsLawful ops observe)
    (compatible : CompatibleProvision.Compatible ops actor component before) :
    let admitted := admit (actor := actor) (choicesOf ops before actor tokens) lawful grammar
    ∃ input : admitted.domain before, admitted.iterator.execute ⟨before, input⟩ = some after :=
  admits_native_run (choose_actual_run landed compatible) grammar lawful compatible

/-- The repaired Lemma 57 for the native finite grammar. The generated
iterator confines every head on its scoped probes, compares the composed
partial inverses, and recovers the observed input on successful runs. -/
theorem lemma57_scoped (choices : Choices ops Name Code) (lawful : OperationsLawful ops observe)
    (grammar : Mediated program component code) (history : List (Outcome Name ops)) :
    let admitted := admit (actor := actor) choices lawful grammar history
    let calculate := fun input : ScopedEffects.State admitted.domain =>
      ScopedRollback.evaluate admitted.iterator (ScopedRollback.Stable.true ops) input trivial
    ScopedConfinement.IteratorConfined component admitted.iterator ∧
    (∀ left right, ScopedEffects.Observed observe (Interface component) left right →
      Iterators.OptionRel (ScopedRollback.Result.Related observe (Interface component))
        (calculate left) (calculate right)) ∧
    (∀ input result, calculate input = some result →
      ∃ restored, result.restore result.output = some restored ∧
        ScopedEffects.Observed observe (Interface component) restored input) := by
  dsimp only
  refine ⟨admit_confined choices lawful grammar history, ?_, ?_⟩
  · intro left right related
    exact ScopedRollback.evaluate_respects _ _ left right trivial trivial related
  · intro input result called
    exact ScopedRollback.evaluate_recovers _ _ input trivial called

end Cordis.Repairs.MediatedAdmission
