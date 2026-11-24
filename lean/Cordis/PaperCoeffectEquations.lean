/-! arXiv:2608.25512v1, Definitions 19–22 and 24–27, pp. 17–21.
These definitions transcribe the operations and their domains independently
of the source interpreter. A partial operation uses Option. Finite support
is the paper's context domain; the pointwise equations also make sense on
arbitrary partial functions, so applications can supply finiteness separately. -/
namespace Cordis.PaperCoeffectEquations
universe u v

/-- Eq. (20). A binding at key k has type V k. -/
abbrev Table {K : Type u} (V : K → Type v) := (k : K) → Option (V k)

end Cordis.PaperCoeffectEquations
