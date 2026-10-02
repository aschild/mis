import MISLocal.ExtractedCollisions

/-! Erasing the dummy private Unit coordinates gives precisely the original
independent fair-matrix sample space used in the concrete collision proofs. -/

open scoped BigOperators Classical
namespace MISLocal
noncomputable section
namespace TreeGeometry

variable {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)

def matrixUnitEquiv : (G.edgeSet → EdgeMatrix k) ≃
    (∀ i, matrixPrivateType G k (fun _ => Unit) i) where
  toFun M i := match i with
    | Sum.inl e => M e
    | Sum.inr _ => ()
  invFun ω e := ω (Sum.inl e)
  left_inv M := rfl
  right_inv ω := by
    funext i
    cases i with
    | inl e => rfl
    | inr v => exact @Subsingleton.elim Unit _ _ _

theorem matrixUnitProbability_map :
    (FiniteProb.pi (matrixPrivateProbability G k (fun _ => FiniteProb.uniform Unit))).map
      (matrixUnitEquiv G k).symm =
      FiniteProb.pi (fun _ : G.edgeSet => FiniteProb.fairBits (Fin k × Fin k)) := by
  ext M
  rw [FiniteProb.map_equiv_weight]
  change (∏ i : G.edgeSet ⊕ V,
    (matrixPrivateProbability G k (fun _ => FiniteProb.uniform Unit) i).weight
      (matrixUnitEquiv G k M i)) = _
  rw [Fintype.prod_sum_type]
  simp only [matrixPrivateProbability,FiniteProb.sumProb,matrixUnitEquiv,Equiv.coe_fn_mk,
    Sum.elim_inl,Sum.elim_inr,FiniteProb.uniform,Fintype.card_unit,Nat.cast_one,inv_one,
    Finset.prod_const_one,mul_one]
  rfl

theorem matrixUnitProbability_prob (P : (G.edgeSet → EdgeMatrix k) → Prop) :
    (FiniteProb.pi (matrixPrivateProbability G k (fun _ => FiniteProb.uniform Unit))).prob
      (fun ω => P (fun e => ω (Sum.inl e))) =
      (FiniteProb.pi (fun _ : G.edgeSet => FiniteProb.fairBits (Fin k × Fin k))).prob P := by
  have h := congrArg (fun μ : FiniteProb (G.edgeSet → EdgeMatrix k) => μ.prob P)
    (matrixUnitProbability_map G k)
  dsimp only at h
  rw [FiniteProb.prob_map] at h
  exact h

end TreeGeometry
end
end MISLocal
