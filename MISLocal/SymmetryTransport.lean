import MISLocal.AncestorSequence
import MISLocal.NestedGiven

/-! Symmetry of actual conditional distributions and the constructed ancestor
sequence. Null fibers are included: both sides use the same fallback marginal.
This is a distribution identity, not an assumed entropy inequality. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

variable {Ω A B C : Type*} [Fintype Ω] [Fintype A] [Fintype B] [Fintype C]

theorem expect_invariant (μ : FiniteProb Ω) (e : Ω → Ω) (he : μ.map e = μ) (f : Ω → ℝ) :
    μ.expect (fun ω => f (e ω)) = μ.expect f := by
  rw [← μ.expect_map e f, he]

theorem prob_invariant (μ : FiniteProb Ω) (e : Ω → Ω) (he : μ.map e = μ) (E : Ω → Prop) :
    μ.prob (fun ω => E (e ω)) = μ.prob E := μ.expect_invariant e he (fun ω => bit (E ω))

theorem map_transport (μ : FiniteProb Ω) (e : Ω → Ω) (he : μ.map e = μ)
    (X X' : Ω → A) (hX : ∀ ω, X' (e ω) = X ω) : μ.map X' = μ.map X := by
  nth_rw 1 [← he]
  rw [map_comp]
  exact congrArg (map μ) (funext hX)

theorem given_map_transport (μ : FiniteProb Ω) (e : Ω → Ω) (he : μ.map e = μ)
    (X X' : Ω → A) (Y Y' : Ω → B) (β : B ≃ B)
    (hX : ∀ ω, X' (e ω) = X ω) (hY : ∀ ω, Y' (e ω) = β (Y ω)) (b : B) :
    (μ.given Y' (β b)).map X' = (μ.given Y b).map X := by
  have hmass : (μ.map Y').weight (β b) = (μ.map Y).weight b := by
    change μ.prob (fun ω => Y' ω = β b) = μ.prob (fun ω => Y ω = b)
    rw [← μ.prob_invariant e he (fun ω => Y' ω = β b)]
    exact μ.prob_congr (fun ω => by rw [hY, β.injective.eq_iff])
  by_cases hb : 0 < (μ.map Y).weight b
  · have hb' : 0 < (μ.map Y').weight (β b) := by rwa [hmass]
    ext a
    rw [given_pair_mass _ X' Y' a (β b) hb', given_pair_mass _ X Y a b hb, hmass]
    congr 1
    change μ.prob (fun ω => (X' ω,Y' ω) = (a,β b)) = μ.prob (fun ω => (X ω,Y ω) = (a,b))
    rw [← μ.prob_invariant e he (fun ω => (X' ω,Y' ω) = (a,β b))]
    apply μ.prob_congr
    intro ω
    simp only [hX, hY, Prod.mk.injEq, β.injective.eq_iff]
  · have hb' : ¬ 0 < (μ.map Y').weight (β b) := by rwa [hmass]
    simp only [given, hb, hb', dif_neg]
    exact μ.map_transport e he X X' hX

theorem keptOutput_transport (μ : FiniteProb Ω) (e : Ω → Ω) (he : μ.map e = μ)
    (U U' : Ω → Option A) (Y Y' : Ω → B) (β : B ≃ B)
    (hU : ∀ ω, U' (e ω) = U ω) (hY : ∀ ω, Y' (e ω) = β (Y ω)) (m : ℕ) (ω : Ω) :
    μ.keptOutput U' Y' m (e ω) = μ.keptOutput U Y m ω := by
  unfold keptOutput
  rw [hU, hY, μ.given_map_transport e he U U' Y Y' β hU hY]

theorem deletedOutput_transport (μ : FiniteProb Ω) (e : Ω → Ω) (he : μ.map e = μ)
    (U U' : Ω → Option A) (Y Y' : Ω → B) (β : B ≃ B)
    (hU : ∀ ω, U' (e ω) = U ω) (hY : ∀ ω, Y' (e ω) = β (Y ω)) (m : ℕ) (ω : Ω) :
    μ.deletedOutput U' Y' m (e ω) = μ.deletedOutput U Y m ω := by
  unfold deletedOutput
  rw [hU, hY, μ.given_map_transport e he U U' Y Y' β hU hY]

theorem survivor_transport (μ : FiniteProb Ω) (e : Ω → Ω) (he : μ.map e = μ)
    (U U' : Ω → Option A) (Y Y' : ℕ → Ω → B) (β : ℕ → B ≃ B)
    (hU : ∀ ω, U' (e ω) = U ω) (hY : ∀ n ω, Y' n (e ω) = β n (Y n ω)) (m n : ℕ) :
    ∀ ω, μ.survivor U' Y' m n (e ω) = μ.survivor U Y m n ω := by
  induction n with
  | zero => exact hU
  | succ n ih => exact μ.keptOutput_transport e he _ _ _ _ (β n) ih (hY n) m

theorem firstDeleted_transport (μ : FiniteProb Ω) (e : Ω → Ω) (he : μ.map e = μ)
    (U U' : Ω → Option A) (Y Y' : ℕ → Ω → B) (β : ℕ → B ≃ B)
    (hU : ∀ ω, U' (e ω) = U ω) (hY : ∀ n ω, Y' n (e ω) = β n (Y n ω)) (m n : ℕ) :
    ∀ ω, μ.firstDeleted U' Y' m n (e ω) = μ.firstDeleted U Y m n ω :=
  μ.deletedOutput_transport e he _ _ _ _ (β n) (μ.survivor_transport e he U U' Y Y' β hU hY m n)
    (hY n) m

theorem entropy_transport (μ : FiniteProb Ω) (e : Ω → Ω) (he : μ.map e = μ)
    (X X' : Ω → A) (α : A ≃ A) (hX : ∀ ω, X' (e ω) = α (X ω)) :
    μ.entropyOf X' = μ.entropyOf X := by
  nth_rw 1 [← he]
  rw [entropyOf_map]
  rw [μ.entropyOf_congr hX]
  exact μ.entropyOf_comp_injective X α α.injective

theorem conditional_entropy_transport (μ : FiniteProb Ω) (e : Ω → Ω) (he : μ.map e = μ)
    (X X' : Ω → A) (Y Y' : Ω → B) (α : A ≃ A) (β : B ≃ B)
    (hX : ∀ ω, X' (e ω) = α (X ω)) (hY : ∀ ω, Y' (e ω) = β (Y ω)) :
    μ.condEntropy X' Y' = μ.condEntropy X Y := by
  unfold condEntropy
  rw [μ.entropy_transport e he (fun ω => (X ω,Y ω)) (fun ω => (X' ω,Y' ω))
      (α.prodCongr β) (fun ω => Prod.ext (hX ω) (hY ω)),
    μ.entropy_transport e he Y Y' β hY]

end FiniteProb
end
end MISLocal
