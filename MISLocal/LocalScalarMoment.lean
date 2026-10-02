import MISLocal.StochasticEntropy
import MISLocal.BernoulliRounding

/-! A scalar overlap bound derived from independent sources and geometric
routing. There is no entropy-inequality premise in the final theorem. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

theorem bool_pair_ext (P Q : FiniteProb (Bool × Bool))
    (hfst : P.prob (fun ab => ab.1=true) = Q.prob (fun ab => ab.1=true))
    (hsnd : P.prob (fun ab => ab.2=true) = Q.prob (fun ab => ab.2=true))
    (hpair : P.prob (fun ab => ab.1=true ∧ ab.2=true) =
      Q.prob (fun ab => ab.1=true ∧ ab.2=true)) : P = Q := by
  have hP := P.total
  have hQ := Q.total
  simp only [prob, expect, Fintype.sum_prod_type, Fintype.sum_bool] at hfst hsnd hpair hP hQ
  norm_num [bit] at hfst hsnd hpair
  ext ab
  rcases ab with ⟨a,b⟩
  cases a <;> cases b <;> linarith

theorem entropyOf_const {Ω A : Type*} [Fintype Ω] [Fintype A] (μ : FiniteProb Ω) (a : A) :
    μ.entropyOf (fun _ => a) = 0 := by
  rw [entropyOf_eq_expect]
  have hm : (μ.map (fun _ => a)).weight a = 1 := by simp [map]
  simp [hm]

theorem condEntropy_const {Ω A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]
    (μ : FiniteProb Ω) (X : Ω → A) (b : B) : μ.condEntropy X (fun _ => b) = μ.entropyOf X := by
  rw [condEntropy, entropyOf_const, sub_zero, entropy_pair_comm]
  exact μ.entropy_deterministic_pair X (fun _ => b)

theorem scalar_overlap_from_sources {I V E B : Type}
    [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V] [Nonempty V]
    [Fintype E] [DecidableEq E] [Fintype B] [DecidableEq B]
    {T : I → Type} [∀ i, Fintype (T i)]
    (P : ∀ i, FiniteProb (T i)) (Y : V → (∀ i, T i) → B) (f : V → B → ℝ)
    (hf0 : ∀ v b, 0 ≤ f v b) (hf1 : ∀ v b, f v b ≤ 1)
    (left right : E → V) (reads : V → Finset I) {d : ℕ}
    (hlocal : ∀ v, ReadsOnly (Y v) (reads v))
    (charge : SourceCharge left right reads (fun _ => ∅) (fun _ => ∅) d)
    (hdegree : ∀ v, (Finset.univ.filter (edgeIncident left right v)).card = d+1)
    (hcard : 2*Fintype.card E = (d+1)*Fintype.card V)
    (hne : ∀ e, right e ≠ left e) (e₀ : E) {p c : ℝ}
    (hmean : ∀ v, (pi P).expect (fun ω => f v (Y v ω)) = p)
    (hmoment : ∀ e, (pi P).expect (fun ω => f (left e) (Y (left e) ω)*f (right e) (Y (right e) ω)) = c) :
    p^2/2-2*binaryEntropy p/((d:ℝ)+1) ≤ c := by
  let K := fun v b => bernoulli (f v b) (hf0 v b) (hf1 v b)
  let ν := (pi P).product (tableProbability K)
  let Z := tableDraw (A := Bool) Y
  have hmeans (v : V) : ν.prob (fun x => Z v x=true) = p :=
    (bernoulli_table_mean (pi P) Y f hf0 hf1 v).trans (hmean v)
  have hmoments (e : E) : ν.prob (fun x => Z (left e) x=true ∧ Z (right e) x=true) = c :=
    (bernoulli_table_moment (pi P) Y f hf0 hf1 _ _ (hne e)).trans (hmoment e)
  have hv (v : V) : ν.entropyOf (Z v) = binaryEntropy p := by
    change (ν.map (Z v)).entropy = _
    rw [bool_entropy]
    exact congrArg binaryEntropy (hmeans v)
  have he (e : E) : ν.entropyOf (fun x => (Z (left e) x,Z (right e) x)) =
      ν.entropyOf (fun x => (Z (left e₀) x,Z (right e₀) x)) := by
    apply congrArg entropy
    apply bool_pair_ext
    · simp only [prob_map, hmeans]
    · simp only [prob_map, hmeans]
    · simp only [prob_map, hmoments]
  have hv' (v : V) : ν.condEntropy (Z v) (fun x => observeInputs (∅ : Finset I) x.1) =
      ν.entropyOf (Z (left e₀)) := by
    have ho : (fun x : (∀ i, T i) × (V → B → Bool) => observeInputs (∅ : Finset I) x.1) =
        (fun _ => fun i => (none : Option (T i))) := by funext x i; simp [observeInputs]
    rw [ho, condEntropy_const, hv, hv]
  have he' (e : E) : ν.condEntropy (fun x => (Z (left e) x,Z (right e) x))
      (fun x => observeInputs (∅ : Finset I) x.1) =
        ν.entropyOf (fun x => (Z (left e₀) x,Z (right e₀) x)) := by
    have ho : (fun x : (∀ i, T i) × (V → B → Bool) => observeInputs (∅ : Finset I) x.1) =
        (fun _ => fun i => (none : Option (T i))) := by funext x i; simp [observeInputs]
    rw [ho, condEntropy_const]
    exact he e
  have ht := symmetric_table_entropy P Y K left right reads (fun _ => ∅) (fun _ => ∅)
    hlocal charge hdegree (by intro v e hve; exact Finset.empty_subset _) hcard hv' he'
  have h := scalar_pair_overlap ν (Z (left e₀)) (Z (right e₀))
    (show (0:ℝ) < (d:ℝ)+1 by positivity) (hmeans _) (hmeans _) (by
      simpa only [add_sub_cancel_right] using ht)
  rwa [hmoments] at h

end FiniteProb
end
end MISLocal
