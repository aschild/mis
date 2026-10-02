import MISLocal.FrequentLabels

/-! Captures may be arbitrarily dependent; only eligibility is independent. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

variable {Ω I A B : Type*} [Fintype Ω] [Fintype I] [Fintype A] [Fintype B]

theorem prob_indexed_conditioning (μ : FiniteProb Ω) (X : Ω → B)
    (E : B → Ω → Prop) :
    (∑ b, (μ.map X).weight b * (μ.given X b).prob (E b)) =
      μ.prob (fun ω => E (X ω) ω) := by
  simp only [prob, μ.weighted_given_expect]
  rw [← μ.expect_sum]
  apply μ.expect_congr
  intro ω
  rw [Finset.sum_eq_single (X ω)]
  · simp [bit]
  · intro b _ hb
    simp [bit, Ne.symm hb]
  · simp

theorem listTail_prob (P : FiniteProb (Option A)) (S : Finset A) :
    P.listTail S = P.prob (fun x => ∃ a, x = some a ∧ a ∉ S) := by
  simp only [listTail, prob, expect, Fintype.sum_option]
  rw [show bit (∃ a, (none : Option A) = some a ∧ a ∉ S) = 0 by simp [bit], mul_zero, zero_add]
  have he (b : A) : bit (∃ a, some b = some a ∧ a ∉ S) = bit (b ∉ S) := by
    congr 1
    simp
  simp only [he]
  calc
    _ = ∑ a ∈ Finset.univ \ S, P.weight (some a) * bit (a ∉ S) := by
      apply Finset.sum_congr rfl
      intro a ha
      simp [bit, (Finset.mem_sdiff.mp ha).2]
    _ = _ := Finset.sum_subset Finset.sdiff_subset (fun a _ ha => by
      have hm : a ∈ S := by simpa using ha
      simp [bit, hm])

omit [Fintype Ω] in
theorem eventCount_partition (E C : I → Ω → Prop) (ω : Ω) :
    eventCount E ω = eventCount (fun i ω => E i ω ∧ C i ω) ω +
      eventCount (fun i ω => E i ω ∧ ¬ C i ω) ω := by
  rw [eventCount, eventCount, eventCount, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hE : E i ω <;> by_cases hC : C i ω <;> simp [bit, hE, hC]

/-- This statement deliberately assumes no independence of `C`. -/
theorem many_eligible_captures (μ : FiniteProb Ω) (E C : I → Ω → Prop)
    (hind : μ.IndependentEvents E) {t : ℝ}
    (hmiss : ∀ i, μ.prob (fun ω => E i ω ∧ ¬ C i ω) ≤ t/2 * μ.prob (E i))
    (hsmall : Real.exp (-μ.eventMean E / 128) ≤ t/12)
    (hmean : 0 < μ.eventMean E) :
    μ.prob (fun ω => eventCount (fun i ω => E i ω ∧ C i ω) ω < μ.eventMean E/8) ≤
      3*t/4 := by
  let U := eventCount (fun i ω => E i ω ∧ ¬ C i ω)
  have hEU : μ.expect U ≤ t/2 * μ.eventMean E := by
    rw [show μ.expect U = ∑ i, μ.prob (fun ω => E i ω ∧ ¬ C i ω) from μ.expect_eventCount _]
    calc
      _ ≤ ∑ i, t/2 * μ.prob (E i) := Finset.sum_le_sum (fun i _ => hmiss i)
      _ = _ := by rw [← Finset.mul_sum]; rfl
  have hbad := μ.prob_mono (p := fun ω =>
    eventCount (fun i ω => E i ω ∧ C i ω) ω < μ.eventMean E/8)
    (q := fun ω => eventCount E ω < 7*μ.eventMean E/8 ∨ 3*μ.eventMean E/4 ≤ U ω) (by
      intro ω hω
      by_cases hL : eventCount E ω < 7*μ.eventMean E/8
      · exact Or.inl hL
      · right
        have heq := eventCount_partition E C ω
        change eventCount E ω = _ + U ω at heq
        linarith)
  have hMarkov := μ.prob_ge_le_expect_div U
    (fun ω => Finset.sum_nonneg (fun i _ => bit_nonneg (E i ω ∧ ¬ C i ω)))
    (show 0 < 3*μ.eventMean E/4 by linarith)
  have hquot : μ.expect U / (3*μ.eventMean E/4) ≤ 2*t/3 := by
    apply (div_le_iff₀ (show 0 < 3*μ.eventMean E/4 by linarith)).mpr
    nlinarith
  have hunion := μ.prob_or_le (fun ω => eventCount E ω < 7*μ.eventMean E/8)
    (fun ω => 3*μ.eventMean E/4 ≤ U ω)
  have hlow := hind.lower_tail
  linarith

def listCaptures (Z : Ω → Option A) (L : Ω → Finset A) (ω : Ω) : Prop :=
  Z ω = none ∨ ∃ a, Z ω = some a ∧ a ∈ L ω

/-- The finite union argument that turns simultaneous capture into one
fixed short list. The sampled output can depend on all the lists. -/
theorem fixed_list_from_many_captures (μ : FiniteProb Ω) (Z : Ω → Option A)
    (L : I → Ω → Finset A) (E : I → Ω → Prop) (B : Finset A) (a : ℝ)
    {u v : ℝ}
    (hcapture : μ.prob (fun ω => eventCount (fun i ω => E i ω ∧ listCaptures Z (L i) ω) ω < a) ≤ u)
    (hfrequent : μ.prob (fun ω => ∃ b, b ∉ B ∧ a ≤ eventCount (fun i ω => b ∈ L i ω) ω) ≤ v) :
    (μ.map Z).listTail B ≤ u + v := by
  rw [listTail_prob, μ.prob_map]
  have hsub := μ.prob_mono (p := fun ω => ∃ b, Z ω = some b ∧ b ∉ B)
    (q := fun ω => eventCount (fun i ω => E i ω ∧ listCaptures Z (L i) ω) ω < a ∨
      ∃ b, b ∉ B ∧ a ≤ eventCount (fun i ω => b ∈ L i ω) ω) (by
      intro ω hω
      obtain ⟨b, hZ, hb⟩ := hω
      by_cases hc : eventCount (fun i ω => E i ω ∧ listCaptures Z (L i) ω) ω < a
      · exact Or.inl hc
      · right
        refine ⟨b, hb, (le_of_not_gt hc).trans ?_⟩
        apply Finset.sum_le_sum
        intro i _
        apply bit_mono
        intro hi
        rcases hi.2 with hnone | ⟨b', hb', hmem⟩
        · simp [hZ] at hnone
        · have he : b = b' := Option.some.inj (hZ.symm.trans hb')
          exact he ▸ hmem)
  have hu := μ.prob_or_le
    (fun ω => eventCount (fun i ω => E i ω ∧ listCaptures Z (L i) ω) ω < a)
    (fun ω => ∃ b, b ∉ B ∧ a ≤ eventCount (fun i ω => b ∈ L i ω) ω)
  linarith

end FiniteProb
end
end MISLocal
