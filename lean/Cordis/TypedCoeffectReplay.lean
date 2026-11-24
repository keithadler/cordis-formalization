import Cordis.PartialReplayHistory

/-! Embed dependent coeffect values in the ordinary registry carrier. A
private probe records the domain of a partial inverse even though its ordinary
value branch uses identity completion. Operation outcomes have their own tag. -/
namespace Cordis.TypedCoeffectReplay

open PartialCoeffectLifting (PartialMap compose)
open PartialReplayHistory (KeyLaws)
open Iterators (OptionRel)
universe u
variable {Key : Type u} {Value : Key → Type u} {Yield : Type u}

abbrev Encoded (Value : Key → Type u) (Yield : Type u) :=
  Sum (Option (Sigma Value)) (Sum (Sigma Value) Yield)

def pack (key : Key) (value : Value key) : Encoded Value Yield :=
  .inl (some ⟨key, value⟩)

def probe (key : Key) (value : Value key) : Encoded Value Yield :=
  .inr (.inl ⟨key, value⟩)

def SigmaRelated (observe : ∀ key, Setoid (Value key)) (a b : Sigma Value) : Prop :=
  ∃ same : a.1 = b.1, (observe b.1).r (same ▸ a.2) b.2

def ValueRelated (observe : ∀ key, Setoid (Value key)) : Encoded Value Yield → Encoded Value Yield → Prop
  | .inl left, .inl right => OptionRel (SigmaRelated observe) left right
  | .inr (.inl left), .inr (.inl right) => SigmaRelated observe left right
  | .inr (.inr left), .inr (.inr right) => left = right
  | _, _ => False

private theorem sigma_refl (observe : ∀ key, Setoid (Value key)) (a : Sigma Value) :
    SigmaRelated observe a a := ⟨rfl, (observe a.1).refl a.2⟩

private theorem sigma_symm (observe : ∀ key, Setoid (Value key)) {a b : Sigma Value}
    (same : SigmaRelated observe a b) : SigmaRelated observe b a := by
  rcases a with ⟨key, left⟩
  rcases b with ⟨other, right⟩
  obtain ⟨tags, relation⟩ := same
  cases tags
  exact ⟨rfl, (observe key).symm relation⟩

private theorem sigma_trans (observe : ∀ key, Setoid (Value key)) {a b c : Sigma Value}
    (earlier : SigmaRelated observe a b) (later : SigmaRelated observe b c) : SigmaRelated observe a c := by
  rcases a with ⟨key, left⟩
  rcases b with ⟨other, middle⟩
  rcases c with ⟨last, right⟩
  obtain ⟨tag, eq⟩ := earlier
  obtain ⟨tag', eq'⟩ := later
  cases tag
  cases tag'
  exact ⟨rfl, (observe key).trans eq eq'⟩

@[simp] theorem packed_related (observe : ∀ key, Setoid (Value key))
    (key : Key) (left right : Value key) :
    ValueRelated observe (pack (Yield := Yield) key left) (pack key right) ↔ (observe key).r left right := by
  constructor
  · rintro ⟨same, related⟩
    exact related
  · exact fun related => ⟨rfl, related⟩

def setoid (observe : ∀ key, Setoid (Value key)) : Setoid (Encoded Value Yield) where
  r := ValueRelated observe
  iseqv := by
    constructor
    · rintro (value | (privateTag | tag))
      · cases value with
        | none => trivial
        | some value => exact sigma_refl observe value
      · exact sigma_refl observe privateTag
      · rfl
    · rintro (left | (privateL | tagL)) (right | (privateR | tagR))
      all_goals try (intro proof; exact proof)
      · intro h
        exact OptionRel.mono (fun _ _ proof => sigma_symm observe proof) (OptionRel.symm h)
      · exact sigma_symm observe
      · exact Eq.symm
    · rintro (left | (privateL | tagL)) (middle | (privateM | tagM)) (right | (privateR | tagR))
      all_goals try (intro first second; exact first.elim)
      all_goals try (intro first second; exact second.elim)
      · exact OptionRel.trans (R := SigmaRelated observe) (fun _ _ _ a b => sigma_trans observe a b)
      · exact sigma_trans observe
      · exact Eq.trans

variable [DecidableEq Key]

private def atKey (key : Key) (input : Sigma Value) : Option (Value key) :=
  if same : input.1 = key then some (same ▸ input.2) else none

def unpack (key : Key) : Encoded Value Yield → Option (Value key)
  | .inl (some value) => atKey key value
  | _ => none

private def unpackProbe (key : Key) : Encoded Value Yield → Option (Value key)
  | .inr (.inl value) => atKey key value
  | _ => none

@[simp] theorem unpack_pack (key : Key) (value : Value key) :
    unpack key (pack (Yield := Yield) key value) = some value := by
  simp [unpack, pack, atKey]

private theorem atKey_recognizes (key : Key) (input : Sigma Value) (value : Value key)
    (found : atKey key input = some value) : input = ⟨key, value⟩ := by
  rcases input with ⟨source, original⟩
  by_cases same : source = key
  · subst source
    have values : original = value := by simpa [atKey] using found
    cases values
    rfl
  · simp [atKey, same] at found

theorem unpack_recognizes (key : Key) (input : Encoded Value Yield) (value : Value key)
    (found : unpack key input = some value) : input = pack key value := by
  rcases input with (_ | tagged) | payload
  · simp [unpack] at found
  · have selected := atKey_recognizes key tagged value found
    cases selected
    rfl
  · simp [unpack] at found

theorem pack_injective (key : Key) : Function.Injective (pack (Value := Value) (Yield := Yield) key) := by
  intro first second equal
  have recognized := congrArg (unpack key) equal
  simpa using recognized

private theorem atKey_related (observe : ∀ key, Setoid (Value key)) (key : Key) {left right : Sigma Value}
    (related : SigmaRelated observe left right) :
    OptionRel (observe key).r (atKey key left) (atKey key right) := by
  rcases left with ⟨source, actual⟩
  rcases right with ⟨target, result⟩
  obtain ⟨same, localRelated⟩ := related
  cases same
  by_cases selected : source = key
  · subst source
    simpa [OptionRel, atKey] using localRelated
  · simp [OptionRel, atKey, selected]

theorem unpack_related (observe : ∀ key, Setoid (Value key)) (key : Key)
    {left right : Encoded Value Yield} (related : ValueRelated observe left right) :
    OptionRel (observe key).r (unpack key left) (unpack key right) := by
  rcases left with (_ | source) | (source | tag) <;> rcases right with (_ | target) | (target | tag')
  all_goals first | exact False.elim related | exact True.intro | exact atKey_related observe key related

private theorem unpackProbe_related (observe : ∀ key, Setoid (Value key)) (key : Key)
    {left right : Encoded Value Yield} (related : ValueRelated observe left right) :
    OptionRel (observe key).r (unpackProbe key left) (unpackProbe key right) := by
  rcases left with value | (source | tag) <;> rcases right with value | (target | tag')
  all_goals first | exact False.elim related | exact True.intro | exact atKey_related observe key related

def liftMap (key : Key) (map : PartialMap (Value key)) : PartialMap (Encoded Value Yield) :=
  fun input => (unpack key input).bind fun value => (map value).map (pack key)

@[simp] theorem liftMap_pack (key : Key) (map : PartialMap (Value key)) (input : Value key) :
    liftMap (Yield := Yield) key map (pack key input) = (map input).map (pack key) := by
  simp [liftMap]

theorem liftMap_compose (key : Key) (first second : PartialMap (Value key)) :
    liftMap (Yield := Yield) key (compose second first) = compose (liftMap key second) (liftMap key first) := by
  funext input
  cases read : unpack key input with
  | none => simp [liftMap, compose, read]
  | some value =>
    cases intermediate : first value <;> simp [liftMap, compose, read, intermediate]

omit [DecidableEq Key] in
private theorem pack_options (observe : ∀ key, Setoid (Value key)) (key : Key) {left right : Option (Value key)}
    (related : OptionRel (observe key).r left right) :
    OptionRel (ValueRelated observe) (left.map (pack (Yield := Yield) key)) (right.map (pack key)) := by
  cases left <;> cases right
  all_goals try exact related.elim
  · trivial
  · exact (packed_related (Yield := Yield) observe key _ _).mpr related

theorem liftMap_related (observe : ∀ key, Setoid (Value key)) (key : Key) {first second : PartialMap (Value key)}
    (respect : PartialInverseObservation.MapRelated (observe key).r first second) :
    PartialInverseObservation.MapRelated (ValueRelated (Yield := Yield) observe)
      (liftMap key first) (liftMap key second) := by
  intro left right related
  have values := unpack_related observe key related
  cases atLeft : unpack key left <;> cases atRight : unpack key right
  · simp [liftMap, atLeft, atRight, OptionRel]
  · simp [atLeft, atRight, OptionRel] at values
  · simp [atLeft, atRight, OptionRel] at values
  · simp only [atLeft, atRight, OptionRel] at values
    simpa only [liftMap, atLeft, atRight, Option.bind_some] using pack_options observe key (respect _ _ values)

/-- At a binding, run the represented partial inverse with identity completion.
At a private probe, its result preserves undefinedness rather than completing it. -/
def encodeMap (key : Key) (map : PartialMap (Value key)) : Encoded Value Yield → Encoded Value Yield :=
  fun input => match unpack key input with
    | some value => pack key ((map value).getD value)
    | none => match unpackProbe key input with
      | some value => ((map value).map (pack key)).getD (.inl none)
      | none => input

@[simp] theorem encodeMap_pack (key : Key) (map : PartialMap (Value key)) (input : Value key) :
    encodeMap (Yield := Yield) key map (pack key input) = pack key ((map input).getD input) := by
  simp [encodeMap]

@[simp] theorem encodeMap_probe (key : Key) (map : PartialMap (Value key)) (input : Value key) :
    encodeMap (Yield := Yield) key map (probe key input) = ((map input).map (pack key)).getD (.inl none) := by
  simp [encodeMap, unpack, probe, unpackProbe, atKey]

/-- Recover a partial map from inverse syntax by probing its actual domain.
The returned value always equals the syntax result at the ordinary binding. -/
def decodeInverse (key : Key) (implementation : Encoded Value Yield → Encoded Value Yield) :
    PartialMap (Encoded Value Yield) :=
  fun input => (unpack key input).bind fun value =>
    (unpack key (implementation (probe key value))).bind fun _ =>
      (unpack key (implementation input)).map fun _ => implementation input

theorem decodeInverse_agrees (key : Key) (implementation : Encoded Value Yield → Encoded Value Yield)
    (input output : Encoded Value Yield) (decoded : decodeInverse key implementation input = some output) :
    implementation input = output := by
  cases read : unpack key input with
  | none => simp [decodeInverse, read] at decoded
  | some value =>
    cases domain : unpack key (implementation (probe key value)) <;>
      cases result : unpack key (implementation input) <;>
      simp [decodeInverse, read, domain, result] at decoded
    exact decoded

/-- The comparison of encoded functions includes the probes that expose
their true domains. Decoding therefore preserves partial-map relatedness. -/
theorem decodeInverse_related (observe : ∀ key, Setoid (Value key)) (key : Key)
    {first second : Encoded Value Yield → Encoded Value Yield}
    (functions : ∀ left right, ValueRelated observe left right → ValueRelated observe (first left) (second right)) :
    PartialInverseObservation.MapRelated (ValueRelated observe)
      (decodeInverse key first) (decodeInverse key second) := by
  intro left right related
  have inputs := unpack_related observe key related
  cases readLeft : unpack key left <;> cases readRight : unpack key right <;>
    simp only [readLeft, readRight, OptionRel] at inputs
  · simp [decodeInverse, readLeft, readRight, OptionRel]
  · rename_i a b
    have checked := unpack_related observe key
      (functions (probe key a) (probe key b) (show ValueRelated observe (probe key a) (probe key b) from ⟨rfl, inputs⟩))
    have results := functions left right related
    have decoded := unpack_related observe key results
    cases firstGuard : unpack key (first (probe key a)) <;>
      cases secondGuard : unpack key (second (probe key b)) <;>
      simp only [firstGuard, secondGuard, OptionRel] at checked
    · simp [decodeInverse, readLeft, readRight, firstGuard, secondGuard, OptionRel]
    · cases firstValue : unpack key (first left) <;> cases secondValue : unpack key (second right) <;>
        simp only [firstValue, secondValue, OptionRel] at decoded
      · simp [decodeInverse, readLeft, readRight, firstValue, secondValue, OptionRel]
      · simpa only [decodeInverse, readLeft, readRight, Option.bind_some, firstGuard, secondGuard,
          firstValue, secondValue, Option.map_some, OptionRel] using results

@[simp] theorem decode_encode (key : Key) (map : PartialMap (Value key)) :
    decodeInverse (Yield := Yield) key (encodeMap key map) = liftMap key map := by
  funext input
  cases read : unpack key input with
  | none => simp [decodeInverse, liftMap, read]
  | some value =>
    rw [unpack_recognizes key input value read]
    cases transformed : map value
    · simp only [decodeInverse, unpack_pack, liftMap_pack, Option.bind_some, encodeMap_probe, transformed,
        Option.map_none, Option.getD_none]
      rfl
    · simp only [decodeInverse, unpack_pack, liftMap_pack, Option.bind_some, encodeMap_probe, encodeMap_pack,
        transformed, Option.map_some, Option.getD_some]

theorem encodeMap_injective (key : Key) : Function.Injective
    (encodeMap (Value := Value) (Yield := Yield) key) := by
  intro first second encoded
  funext input
  have mapped := congrFun (congrArg (decodeInverse key) encoded) (pack key input)
  rw [decode_encode, decode_encode, liftMap_pack, liftMap_pack] at mapped
  have decoded := congrArg (fun result => result.bind (unpack key)) mapped
  cases left : first input <;> cases right : second input <;> simp [left, right] at decoded ⊢
  exact decoded

/-- The two completions of related partial maps remain related as total maps
on the tagged carrier, including their private probes. -/
theorem encodeMap_related (observe : ∀ key, Setoid (Value key)) (key : Key)
    {first second : PartialMap (Value key)}
    (respect : PartialInverseObservation.MapRelated (observe key).r first second) :
    ∀ left right, ValueRelated observe left right →
      ValueRelated (Yield := Yield) observe (encodeMap key first left) (encodeMap key second right) := by
  intro left right related
  have ordinary := unpack_related observe key related
  cases a : unpack key left <;> cases b : unpack key right
  · have privateValues := unpackProbe_related observe key related
    cases aProbe : unpackProbe key left <;> cases bProbe : unpackProbe key right
    · simpa only [encodeMap, a, b, aProbe, bProbe] using related
    · simp [aProbe, bProbe, OptionRel] at privateValues
    · simp [aProbe, bProbe, OptionRel] at privateValues
    · rename_i x y
      have matched : (observe key).r x y := by simpa only [aProbe, bProbe, OptionRel] using privateValues
      have outputs := respect x y matched
      cases firstResult : first x <;> cases secondResult : second y
      · simp only [encodeMap, a, b, aProbe, bProbe, firstResult, secondResult]
        trivial
      · simp [firstResult, secondResult, OptionRel] at outputs
      · simp [firstResult, secondResult, OptionRel] at outputs
      · simpa only [encodeMap, a, b, aProbe, bProbe, firstResult, secondResult, Option.map_some, Option.getD_some,
          packed_related, OptionRel] using outputs
  · simp [a, b, OptionRel] at ordinary
  · simp [a, b, OptionRel] at ordinary
  · rename_i x y
    have matched : (observe key).r x y := by simpa only [a, b, OptionRel] using ordinary
    have outputs := respect x y matched
    cases firstResult : first x <;> cases secondResult : second y
    · simpa only [encodeMap, a, b, firstResult, secondResult, Option.getD_none, packed_related] using matched
    · simp [firstResult, secondResult, OptionRel] at outputs
    · simp [firstResult, secondResult, OptionRel] at outputs
    · simpa only [encodeMap, a, b, firstResult, secondResult, Option.getD_some, packed_related, OptionRel] using outputs

def Lifted (admitted : ∀ key, PartialMap (Value key) → Prop)
    (key : Key) (map : PartialMap (Encoded Value Yield)) : Prop :=
  ∃ source, admitted key source ∧ map = liftMap key source

/-- Definition 46's key laws transport to the common tagged carrier.
At a mismatched key the two partial applications are both undefined. -/
theorem lift_key_laws (observe : ∀ key, Setoid (Value key))
    (admitted : ∀ key, PartialMap (Value key) → Prop) (key : Key)
    (laws : KeyLaws (observe key) (admitted key)) :
    KeyLaws (setoid (Yield := Yield) observe) (Lifted admitted key) := by
  constructor
  · rintro map ⟨source, allowed, rfl⟩
    exact liftMap_related observe key (laws.respects source allowed)
  · rintro first second ⟨a, allowedA, rfl⟩ ⟨b, allowedB, rfl⟩
    change PartialInverseObservation.MapRelated (ValueRelated observe)
      (compose (liftMap key a) (liftMap key b)) (compose (liftMap key b) (liftMap key a))
    rw [← liftMap_compose, ← liftMap_compose]
    exact liftMap_related observe key (laws.commutes a b allowedA allowedB)

end Cordis.TypedCoeffectReplay
