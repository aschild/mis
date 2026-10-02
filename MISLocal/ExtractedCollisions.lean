import MISLocal.IdentifierBits
import MISLocal.LocalBallCounts

/-! Apply the proved joint distribution, rather than assume independence of
the tentative IDs. Difference of two coordinates is uniform in the bit group. -/

open scoped BigOperators Classical
namespace MISLocal
noncomputable section

def coordinateDifference {I A : Type*} [AddCommGroup A] (i j : I) : (I → A) →+ A where
  toFun x := x i-x j
  map_zero' := by simp
  map_add' := by intros; simp; abel

theorem coordinateDifference_surjective {I A : Type*} [AddCommGroup A]
    {i j : I} (hij : i ≠ j) : Function.Surjective (coordinateDifference (A := A) i j) := by
  intro a
  refine ⟨Function.update (fun _ => 0) i a,?_⟩
  simp [coordinateDifference,hij.symm]

namespace FiniteProb

theorem uniform_point {A : Type*} [Fintype A] [Nonempty A] (a : A) :
    (uniform A).prob (fun x => x = a) = (Fintype.card A : ℝ)⁻¹ := by
  simp [prob,expect,uniform,bit]

theorem uniform_group_collision {I A : Type*} [Fintype I] [Fintype A]
    [DecidableEq I] [AddCommGroup A] {i j : I} (hij : i ≠ j) :
    (uniform (I → A)).prob (fun x => x i = x j) = (Fintype.card A : ℝ)⁻¹ := by
  have hd := uniform_map_surjective_addHom (coordinateDifference (A := A) i j)
    (coordinateDifference_surjective hij)
  have hp := congrArg (fun μ : FiniteProb A => μ.prob (fun a => a = 0)) hd
  dsimp only at hp
  rw [prob_map,uniform_point] at hp
  simpa only [coordinateDifference,AddMonoidHom.coe_mk,ZeroHom.coe_mk,sub_eq_zero] using hp

theorem uniform_identifier_collision {I : Type*} [Fintype I] [DecidableEq I] (b : ℕ)
    {i j : I} (hij : i ≠ j) :
    (uniform (I → Fin (2^b))).prob (fun x => x i = x j) = 1/(2^b : ℕ) := by
  have hm := uniform_map_equiv (wordsIdentifierEquiv (X := I) b)
  have hp := congrArg (fun μ : FiniteProb (I → Fin (2^b)) => μ.prob (fun x => x i = x j)) hm
  dsimp only at hp
  rw [prob_map] at hp
  have he (x : I → Fin b → ZMod 2) :
      wordsIdentifierEquiv b x i = wordsIdentifierEquiv b x j ↔ x i = x j :=
    (wordIdentifierEquiv b).injective.eq_iff
  rw [prob_congr _ he,uniform_group_collision hij] at hp
  rw [← hp]
  simp [ZMod.card,one_div]

end FiniteProb

namespace TreeGeometry
variable {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {m b : ℕ}
    (pack : (Fin (2*m) × Fin b) ↪ (Fin m × Fin m))

theorem extractedIdentifier_collision (hdegree : ∀ v, 0 < G.degree v)
    {x y : V × Fin (2*m)} (hxy : x ≠ y) :
    (FiniteProb.pi (fun _ : G.edgeSet => FiniteProb.fairBits (Fin (2*m) × Fin (2*m)))).prob
      (fun M => extractedIdentifiers G pack M x = extractedIdentifiers G pack M y) = 1/(2^b : ℕ) := by
  have hp := congrArg (fun μ : FiniteProb ((V × Fin (2*m)) → Fin (2^b)) =>
    μ.prob (fun ids => ids x = ids y)) (extractedIdentifiers_jointly_uniform G pack hdegree)
  dsimp only at hp
  rw [FiniteProb.prob_map,FiniteProb.uniform_identifier_collision b hxy] at hp
  exact hp

theorem extracted_local_collision_bound (hdegree : ∀ v, 0 < G.degree v)
    (t : ℕ) (root : V) :
    (FiniteProb.pi (fun _ : G.edgeSet => FiniteProb.fairBits (Fin (2*m) × Fin (2*m)))).prob
      (fun M => ¬Set.InjOn (extractedIdentifiers G pack M) {z | InBall G t root z.1}) ≤
      ((ballFinset G t root).card*(2*m) : ℕ) *
        (((ballFinset G t root).card*(2*m) : ℕ) - (1:ℝ)) / (2^b : ℕ) := by
  let I := {z : V × Fin (2*m) // InBall G t root z.1}
  have hn : 0 < 2^b := by positivity
  have hi := local_collision_bound
    (FiniteProb.pi (fun _ : G.edgeSet => FiniteProb.fairBits (Fin (2*m) × Fin (2*m))))
    (fun i : I => fun M => extractedIdentifiers G pack M i.val) (2^b) hn
    (fun i j hij => by
      rw [extractedIdentifier_collision G pack hdegree (fun h => hij (Subtype.ext h))]
      have hp : (0:ℝ) < (2^b : ℕ) := by positivity
      exact div_le_div_of_nonneg_right (by norm_num : (1:ℝ) ≤ 2) hp.le)
  have he (M : G.edgeSet → EdgeMatrix (2*m)) :
      Function.Injective (fun i : I => extractedIdentifiers G pack M i.val) ↔
        Set.InjOn (extractedIdentifiers G pack M) {z | InBall G t root z.1} := by
    constructor
    · intro h x hx y hy hxy
      exact congrArg Subtype.val (h (show extractedIdentifiers G pack M (⟨x,hx⟩ : I) =
        extractedIdentifiers G pack M (⟨y,hy⟩ : I) from hxy))
    · intro h x y hxy
      exact Subtype.ext (h x.property y.property hxy)
  rw [FiniteProb.prob_congr _ (fun M => not_congr (he M)),cliqueBall_card G root] at hi
  exact hi

end TreeGeometry
end
end MISLocal
