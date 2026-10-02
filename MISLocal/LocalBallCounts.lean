import MISLocal.GraphViewTransport

/-! Elementary ball-size bounds, with no truncated subtraction. -/

open scoped BigOperators Classical
namespace MISLocal
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]

def ballFinset (t : ℕ) (v : V) : Finset V := Finset.univ.filter (InBall G t v)

omit [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem mem_ballFinset (t : ℕ) (v w : V) :
    w ∈ ballFinset G t v ↔ InBall G t v w := by simp [ballFinset]

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem ballFinset_zero (v : V) : ballFinset G 0 v = {v} := by
  ext w; simp [InBall]

theorem ballFinset_succ (t : ℕ) (v : V) :
    ballFinset G (t+1) v = insert v ((G.neighborFinset v).biUnion (ballFinset G t)) := by
  ext w
  simp [InBall]

theorem ballFinset_card_le {D : ℕ} (hD : ∀ v, G.degree v ≤ D) (t : ℕ) (v : V) :
    (ballFinset G t v).card ≤ (D+1)^t := by
  induction t generalizing v with
  | zero => simp [ballFinset_zero G v]
  | succ t ih =>
    rw [ballFinset_succ G t v]
    have hsum : (∑ w ∈ G.neighborFinset v, (ballFinset G t w).card) ≤ D*(D+1)^t := by
      calc
        _ ≤ ∑ _w ∈ G.neighborFinset v, (D+1)^t := Finset.sum_le_sum (fun w _ => ih w)
        _ = G.degree v * (D+1)^t := by simp
        _ ≤ _ := Nat.mul_le_mul_right _ (hD v)
    have hp : 1 ≤ (D+1)^t := Nat.one_le_pow _ _ (by omega)
    calc
      _ ≤ ((G.neighborFinset v).biUnion (ballFinset G t)).card+1 := Finset.card_insert_le _ _
      _ ≤ D*(D+1)^t+1 := Nat.add_le_add_right ((Finset.card_biUnion_le).trans hsum) _
      _ ≤ (D+1)^(t+1) := by rw [pow_succ]; nlinarith

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem cliqueBall_card {k t : ℕ} (v : V) :
    Fintype.card {z : V × Fin k // InBall G t v z.1} = (ballFinset G t v).card*k := by
  let e : {z : V × Fin k // InBall G t v z.1} ≃
      {w : V // w ∈ ballFinset G t v} × Fin k :=
    { toFun z := (⟨z.val.1,(mem_ballFinset G t v z.val.1).mpr z.property⟩,z.val.2)
      invFun z := ⟨(z.1.val,z.2),(mem_ballFinset G t v z.1.val).mp z.1.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  rw [Fintype.card_congr e,Fintype.card_prod,Fintype.card_coe,Fintype.card_fin]

end
end MISLocal
