import MISLocal.FairBitProjection
import MISLocal.ExtractedCollisions
import MISLocal.ConditionalSources

/-! A fixed external choice must hit every independently sampled root row.
This estimate quantifies over fixed choices before seeing any matrix. -/

open scoped BigOperators Classical
namespace MISLocal
noncomputable section
namespace FiniteProb

def curryBitEquiv (A B : Type*) : ((A × B) → Bool) ≃ (A → B → Bool) where
  toFun x a b := x (a,b)
  invFun x p := x p.1 p.2
  left_inv _ := rfl
  right_inv _ := rfl

theorem fairBits_row_hit {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] :
    (fairBits (A × B)).prob (fun x => ∀ a, ∃ b, x (a,b) = true) =
      (1-(2:ℝ)^(-(Fintype.card B:ℤ)))^(Fintype.card A) := by
  have hfalse : (fairBits B).prob (fun x => ∀ b, x b = false) =
      (2:ℝ)^(-(Fintype.card B:ℤ)) := by
    have he (x : B → Bool) : (∀ b, x b = false) ↔ x = fun _ => false := by
      constructor
      · exact fun h => funext h
      · intro h b; simp only [h]
    rw [prob_congr _ he]
    have hu : fairBits B = uniform (B → Bool) := pi_uniform
    rw [hu,uniform_point]
    simp [zpow_neg,Fintype.card_fun]
  have hrow : (fairBits B).prob (fun x => ∃ b, x b = true) =
      1-(2:ℝ)^(-(Fintype.card B:ℤ)) := by
    have he (x : B → Bool) : (∃ b, x b = true) ↔ ¬(∀ b, x b = false) := by
      simp only [not_forall,Bool.not_eq_false]
    rw [prob_congr _ he,prob_not,hfalse]
  have hm : (fairBits (A × B)).map (curryBitEquiv A B) = pi (fun _ : A => fairBits B) := by
    have huAB : fairBits (A × B) = uniform ((A × B) → Bool) := pi_uniform
    have huB : fairBits B = uniform (B → Bool) := pi_uniform
    rw [huAB,uniform_map_equiv,huB,pi_uniform]
  have he (x : A → B → Bool) : bit (∀ a, ∃ b, x a b = true) =
      ∏ a, bit (∃ b, x a b = true) := by
    by_cases h : ∀ a, ∃ b, x a b = true
    · simp [bit,h]
    · obtain ⟨a,ha⟩ := not_forall.mp h
      rw [Finset.prod_eq_zero (Finset.mem_univ a) (by simp [bit,ha])]
      simp [bit,h]
  have hp := congrArg (fun μ : FiniteProb (A → B → Bool) => μ.prob (fun x => ∀ a, ∃ b, x a b=true)) hm
  dsimp only at hp
  rw [prob_map] at hp
  change (fairBits (A × B)).prob (fun x => ∀ a, ∃ b, x (a,b)=true) = _ at hp
  rw [hp]
  change (pi (fun _ : A => fairBits B)).expect (fun x => bit (∀ a, ∃ b, x a b=true)) = _
  rw [expect_congr _ he,expect_pi_prod (fun _ : A => fairBits B)
    (fun _ row => bit (∃ b, row b=true))]
  change (∏ _a : A, (fairBits B).prob (fun x => ∃ b, x b=true)) = _
  simp [hrow]

theorem fixed_domination_probability {A B J : Type*} [Fintype A] [Fintype B] [Fintype J]
    [DecidableEq A] [DecidableEq B] [DecidableEq J] (f : (A × B) ↪ J)
    {D : ℕ} (hB : Fintype.card B ≤ D) :
    (fairBits J).prob (fun x => ∀ a, ∃ b, x (f (a,b))=true) ≤
      Real.exp (-(Fintype.card A:ℝ)*(2:ℝ)^(-(D:ℤ))) := by
  have hm := fairBits_map_restriction f
  have hp := congrArg (fun μ : FiniteProb ((A × B) → Bool) =>
    μ.prob (fun x => ∀ a, ∃ b, x (a,b)=true)) hm
  dsimp only at hp
  rw [prob_map,fairBits_row_hit] at hp
  rw [hp]
  have hq : (2:ℝ)^(-(D:ℤ)) ≤ (2:ℝ)^(-(Fintype.card B:ℤ)) := by
    apply zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2)
    exact neg_le_neg (by exact_mod_cast hB)
  have hn : 0 ≤ 1-(2:ℝ)^(-(Fintype.card B:ℤ)) := by
    have hu : (2:ℝ)^(-(Fintype.card B:ℤ)) ≤ (2:ℝ)^(0:ℤ) :=
      zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega)
    exact sub_nonneg.mpr (by simpa only [zpow_zero] using hu)
  have he : 1-(2:ℝ)^(-(Fintype.card B:ℤ)) ≤ Real.exp (-(2:ℝ)^(-(D:ℤ))) := by
    linarith [Real.add_one_le_exp (-(2:ℝ)^(-(D:ℤ)))]
  calc
    _ ≤ (Real.exp (-(2:ℝ)^(-(D:ℤ))))^(Fintype.card A) := pow_le_pow_left₀ hn he _
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

end FiniteProb
end
end MISLocal
