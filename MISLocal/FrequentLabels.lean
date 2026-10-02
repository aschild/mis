import MISLocal.IndependentEvents

/-!
# Consolidating independent short lists

The exponential estimate keeps a factor of the mean. Consequently a union
bound over labels depends on the sum of their weights, not alphabet size.
-/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section

theorem exp_sub_one_le_mul_exp (x : ℝ) : Real.exp x - 1 ≤ x * Real.exp x := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-x)) (Real.exp_pos x).le
  have he : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  rw [he] at h
  nlinarith

namespace FiniteProb

variable {Ω I A : Type*} [Fintype Ω] [Fintype I] [Fintype A]

/-- An upper tail with an essential mean prefactor. -/
theorem IndependentEvents.upper_tail_with_mean {μ : FiniteProb Ω}
    {E : I → Ω → Prop} (h : μ.IndependentEvents E) {a : ℝ} (ha : 1 ≤ a) :
    μ.prob (fun ω => a ≤ eventCount E ω) ≤
      4 * μ.eventMean E * Real.exp (2 * μ.eventMean E - a) := by
  have he1 : Real.exp 1 - 1 ≤ (2:ℝ) := by
    have he := Real.abs_exp_sub_one_le (x := (1:ℝ)) (by norm_num)
    exact (le_abs_self _).trans (by simpa using he)
  have hmean := μ.eventMean_nonneg E
  have he := (h.exp_expect_le 1).trans (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right he1 hmean))
  simp only [one_mul] at he
  have h2 : (2:ℝ) ≤ Real.exp a := by
    have h1 := Real.add_one_le_exp (1:ℝ)
    have hm := Real.exp_le_exp.mpr ha
    linarith
  have hp : (Real.exp a / 2) * μ.prob (fun ω => a ≤ eventCount E ω) ≤
      μ.expect (fun ω => Real.exp (eventCount E ω) - 1) := by
    rw [prob, ← μ.expect_mul]
    apply μ.expect_mono
    intro ω
    have hn : 0 ≤ eventCount E ω := Finset.sum_nonneg (fun i _ => bit_nonneg (E i ω))
    by_cases hω : a ≤ eventCount E ω
    · simp only [bit, if_pos hω, mul_one]
      have hm := Real.exp_le_exp.mpr hω
      linarith
    · simp only [bit, if_neg hω, mul_zero]
      have hm := Real.exp_le_exp.mpr hn
      simpa using sub_nonneg.mpr hm
  rw [μ.expect_sub, μ.expect_const] at hp
  have hp' : μ.prob (fun ω => a ≤ eventCount E ω) ≤
      4 * μ.eventMean E * Real.exp (2 * μ.eventMean E) / Real.exp a := by
    apply (le_div_iff₀ (Real.exp_pos a)).mpr
    nlinarith [exp_sub_one_le_mul_exp (2 * μ.eventMean E)]
  simpa only [Real.exp_sub, mul_div_assoc] using hp'

def labelWeight (μ : FiniteProb Ω) (L : I → Ω → Finset A) (a : A) : ℝ :=
  μ.eventMean (fun i ω => a ∈ L i ω)

def totalListWeight (μ : FiniteProb Ω) (L : I → Ω → Finset A) : ℝ :=
  ∑ a, μ.labelWeight L a

theorem totalListWeight_eq (μ : FiniteProb Ω) (L : I → Ω → Finset A) :
    μ.totalListWeight L = ∑ i, μ.expect (fun ω => ((L i ω).card : ℝ)) := by
  unfold totalListWeight labelWeight eventMean prob
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← μ.expect_sum]
  apply μ.expect_congr
  intro ω
  classical
  have hs := Finset.sum_subset (f := fun x => bit (x ∈ L i ω))
    (Finset.subset_univ (L i ω)) (fun x _ hx => by simp [bit, hx])
  rw [← hs]
  calc
    _ = ∑ _x ∈ L i ω, (1:ℝ) :=
      Finset.sum_congr rfl (fun x hx => by simp [bit, hx])
    _ = _ := by simp

/-- At most `M` fixed labels contain all labels that occur in many independent
lists, except with the stated probability. The lists need not be identically
distributed, and the sampled output may depend on every list. -/
theorem frequent_label_bound (μ : FiniteProb Ω) (L : I → Ω → Finset A)
    (hind : μ.Independent L) {M : ℕ} (hM : 0 < M) {a : ℝ} (ha : 1 ≤ a) :
    μ.prob (fun ω => ∃ b, b ∉ bestList (μ.labelWeight L) M ∧
      a ≤ eventCount (fun i ω => b ∈ L i ω) ω) ≤
      4 * μ.totalListWeight L * Real.exp (2 * μ.totalListWeight L / M - a) := by
  let C := μ.totalListWeight L
  let B := bestList (μ.labelWeight L) M
  have hw (b : A) : 0 ≤ μ.labelWeight L b := μ.eventMean_nonneg _
  have hout (b : A) (hb : b ∉ B) : μ.labelWeight L b ≤ C / M :=
    bestList_outside_le _ M hM hw hb
  have hbnd (b : A) : μ.prob (fun ω => b ∉ B ∧
      a ≤ eventCount (fun i ω => b ∈ L i ω) ω) ≤
      4 * μ.labelWeight L b * Real.exp (2*C/M-a) := by
    by_cases hb : b ∈ B
    · simp only [hb, not_true_eq_false, false_and, prob_false]
      exact mul_nonneg (mul_nonneg (by norm_num) (hw b)) (Real.exp_pos _).le
    · simp only [hb, not_false_eq_true, true_and]
      have he := (hind.events (fun _ S => b ∈ S)).upper_tail_with_mean ha
      apply he.trans
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) (hw b))
      apply Real.exp_le_exp.mpr
      have hh := hout b hb
      change μ.eventMean (fun i ω => b ∈ L i ω) ≤ C / M at hh
      nlinarith only [hh, show 2*C/(M:ℝ) = 2*(C/M) by ring]
  calc
    _ ≤ ∑ b, μ.prob (fun ω => b ∉ B ∧ a ≤ eventCount (fun i ω => b ∈ L i ω) ω) :=
      μ.prob_exists_le_sum _
    _ ≤ ∑ b, 4 * μ.labelWeight L b * Real.exp (2*C/M-a) :=
      Finset.sum_le_sum (fun b _ => hbnd b)
    _ = _ := by simp [totalListWeight, C, ← Finset.sum_mul, ← Finset.mul_sum]

end FiniteProb
end
end MISLocal
