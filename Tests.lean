import MISLocal

/-! Kernel-checked regression examples for boundary cases and repair semantics. -/

open MISLocal

example : (1 - 2 : ℕ) = 0 := by decide
example : (1 : ℝ) - 2 = -1 := by norm_num

example : (0 : ℝ) * ((0 : ℝ) - 1) = 0 := by norm_num
example : (1 : ℝ) * ((1 : ℝ) - 1) = 0 := by norm_num

example (n : ℕ) : ((n - n : ℕ) : ℝ) = 0 := by simp

/-- An edgeless graph really does keep all candidates. -/
example {V : Type*} (S : Set V) : repair (⊥ : SimpleGraph V) S = S := by
  apply repair_of_independent
  intro v hv w hw hne hAdj
  exact hAdj

/-- Two adjacent candidates really are both deleted. -/
example : repair (⊤ : SimpleGraph (Fin 2)) Set.univ = ∅ := by
  ext v
  simp only [repair, Set.mem_setOf_eq, Set.mem_univ, true_and,
    Set.mem_empty_iff_false, iff_false]
  intro h
  fin_cases v
  · exact h 1 (by decide) True.intro
  · exact h 0 (by decide) True.intro

/-- A single coordinate is vacuously collision-free. -/
example {Ω ID : Type*} (X : Fin 1 → Ω → ID) (ω : Ω) :
    Function.Injective (fun i => X i ω) := by
  intro i j _
  exact Subsingleton.elim i j

/-- Empty local views do not require a positive cardinality assumption. -/
example (f : Fin 3 → Fin 3) : Function.Bijective (completeIDs ∅ f) :=
  completeIDs_bijective ∅ f

/-- Collision subtraction is explicitly real; L=0 is not excluded by accident. -/
example : 0 ≤ (0 : ℝ) * ((0 : ℝ) - 1) := by
  norm_num

/-- The round index T+3 does not underflow even at T=0. -/
example : occupancyCap (0 + 3) 10 = min 1 (15000 * Real.log 10 / 10) := by
  norm_num [occupancyCap]

/-- Zero-mass entropy expressions use the continuous extension. -/
example (m : ℝ) : massBudget m 0 = 0 := massBudget_zero m

/-- Logarithm conventions alone do NOT implement infinite relative entropy:
disjoint point masses have real-valued `kl` zero, but are not dominated. -/
example : (FiniteProb.pointMass false).kl (FiniteProb.pointMass true) = 0 := by
  simp [FiniteProb.kl, FiniteProb.pointMass, bit, Fintype.sum_bool]

example : ¬(FiniteProb.pointMass false).Dominated (FiniteProb.pointMass true) := by
  intro h
  have hh := h false (by simp [FiniteProb.pointMass, bit])
  norm_num [FiniteProb.pointMass, bit] at hh

example : (FiniteProb.pointMass true).prob (fun b => b = true) = 1 := by
  simp [bit]

/-- Therefore dropping the support premise from zero_event_le_kl would be false. -/
example : ¬((FiniteProb.pointMass true).prob (fun b => b = true) ≤
    (FiniteProb.pointMass false).kl (FiniteProb.pointMass true)) := by
  simp [FiniteProb.kl, FiniteProb.pointMass, bit, FiniteProb.prob, FiniteProb.expect,
    Fintype.sum_bool]

/-- Conditional entropy of an already-known variable is exactly zero. -/
example (μ : FiniteProb Bool) : μ.condEntropy id id = 0 :=
  μ.condEntropy_deterministic id id

/-- A null conditioning fiber still yields a normalized distribution. -/
example : (FiniteProb.given (FiniteProb.pointMass false) id true).weight false = 1 := by
  simp [FiniteProb.given, FiniteProb.map, FiniteProb.pointMass, FiniteProb.prob,
    FiniteProb.expect, bit, Fintype.sum_bool]

/-- Zero-round local computation sees just the root's input. -/
example {V Input State : Type*} (G : SimpleGraph V) (A : LocalProtocol G Input State)
    (v : V) (x y : V → Input) (h : x v = y v) : A.run x 0 v = A.run y 0 v := by
  exact A.run_local 0 v x y (fun u hu => by cases hu; exact h)

/-- Always selecting the sole available label conflicts on exactly half the matrices. -/
example :
    ((FiniteProb.uniform (Fin 1 × Fin 1 → Bool)).product
      ((FiniteProb.pointMass (some (0 : Fin 1))).product
        (FiniteProb.pointMass (some (0 : Fin 1))))).prob
      (selectedConflict (fun G a b => G (a,b) = true)) = 1/2 := by
  simpa [bit] using zero_radius_conflict (A := Fin 1) (FiniteProb.pointMass (some (0 : Fin 1)))

/-- A list larger than the alphabet has zero omitted mass, even when the
maximizer's tie-breaking does not literally choose every zero-weight label. -/
example (μ : FiniteProb (Option (Fin 2))) : μ.tail 100 = 0 := by
  have h := μ.tail_minimal 100 Finset.univ (by simp)
  have hz : μ.listTail Finset.univ = 0 := by simp [FiniteProb.listTail]
  exact le_antisymm (by simpa only [hz] using h) (μ.listTail_nonneg _)

/-- The graph-radius conversion is only used below the last layer. -/
example (n j : ℕ) (hj : j < n+1) : n+1-j = (n+1-(j+1))+1 := by omega

/-- The last view really contains no raw edges. -/
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (n : ℕ) (v : V) :
    TreeGeometry.seen G (n+1-(n+1)) v = ∅ := by simp [TreeGeometry.seen]

/-- Adding independent private draws does not reveal them in the final view. -/
example {I V E : Type} [DecidableEq I] [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] {d r : ℕ} (g : ProductInputGeometry I V E d r) (v : V) :
    g.withPrivate.vertex r v = ∅ := g.withPrivate.empty_last v

/-- The strong degree/clique-size regime is not silently applicable to k=1. -/
example (D : ℝ) (hD : 1 ≤ D) : ¬ D ≤ Real.log (1:ℝ) := by
  rw [Real.log_one]
  linarith

/-- Skeleton names 0 and 1 cannot distinguish roots in a zero-round rule.
This test does not assume regularity, graph automorphisms or view symmetry. -/
example (G : SimpleGraph (Fin 2)) [DecidableRel G.Adj]
    (A : AnonymousRule (Fin 2) G.edgeSet 1 Unit)
    (x y : ∀ i, TreeGeometry.matrixPrivateType G 1 (fun _ => Unit) i) :
    TreeGeometry.runAnonymous G A 0 0 x = TreeGeometry.runAnonymous G A 0 1 y :=
  TreeGeometry.runAnonymous_zero_same_coin G A 0 1 x y (by
    change (x (Sum.inr 0) : Unit) = (y (Sum.inr 1) : Unit)
    exact @Subsingleton.elim Unit _ (x (Sum.inr 0)) (y (Sum.inr 1)))
