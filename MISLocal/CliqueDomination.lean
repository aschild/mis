import MISLocal.FairRowDomination
import MISLocal.SnapshotLocality

/-! External domination of a clique is rare. One label is chosen in each
neighboring clique before applying the independent-row estimate, and then a
union bound includes every such choice, including matrix-dependent outputs. -/

open scoped BigOperators Classical
namespace MISLocal
noncomputable section

def flatMatrixEquiv (E : Type*) (k : ℕ) :
    (E → EdgeMatrix k) ≃ ((E × (Fin k × Fin k)) → Bool) where
  toFun M z := M z.1 z.2
  invFun x e p := x (e,p)
  left_inv _ := rfl
  right_inv _ := rfl

namespace FiniteProb
theorem fairMatrices_map_flat {E : Type*} [Fintype E] [DecidableEq E] (k : ℕ) :
    (pi (fun _ : E => fairBits (Fin k × Fin k))).map (flatMatrixEquiv E k) =
      fairBits (E × (Fin k × Fin k)) := by
  have hmatrix : fairBits (Fin k × Fin k) = uniform (EdgeMatrix k) := pi_uniform
  have hflat : fairBits (E × (Fin k × Fin k)) = uniform ((E × (Fin k × Fin k)) → Bool) := pi_uniform
  rw [hmatrix,pi_uniform,uniform_map_equiv,hflat]
end FiniteProb

namespace TreeGeometry
variable {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}

def neighborEdge (v : V) (w : G.neighborSet v) : G.edgeSet := ⟨s(v,w.val),w.property⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem neighborEdge_ends (v : V) (w : G.neighborSet v) :
    (edgeLeft G (neighborEdge G v w) = v ∧ edgeRight G (neighborEdge G v w) = w.val) ∨
      (edgeLeft G (neighborEdge G v w) = w.val ∧ edgeRight G (neighborEdge G v w) = v) :=
  Sym2.eq_iff.mp (edge_endpoints G (neighborEdge G v w))

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem neighborEdge_injective (v : V) : Function.Injective (neighborEdge G v) := by
  intro w z h
  have he : s(v,w.val) = s(v,z.val) := congrArg Subtype.val h
  exact Subtype.ext (Sym2.congr_right.mp he)

def neighborPosition (v : V) (w : G.neighborSet v) (a b : Fin k) : Fin k × Fin k :=
  if edgeLeft G (neighborEdge G v w) = v then (a,b) else (b,a)

omit [Fintype V] [DecidableRel G.Adj] in
theorem adjacent_neighbor_entry (M : G.edgeSet → EdgeMatrix k) (v : V)
    (w : G.neighborSet v) (a b : Fin k)
    (h : (cliqueBlowup G M).Adj (v,a) (w.val,b)) :
    M (neighborEdge G v w) (neighborPosition G v w a b) = true := by
  rcases h with h | ⟨e,h⟩
  · exact False.elim (w.property.ne h.1)
  · have hi : edgeIncident (edgeLeft G) (edgeRight G) v e :=
      h.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
    have hw : edgeIncident (edgeLeft G) (edgeRight G) w.val e :=
      h.elim (fun h => Or.inr h.2.1) (fun h => Or.inl h.2.1)
    have he : e = neighborEdge G v w := Subtype.ext (edge_eq_of_incident G w.property.ne e hi hw)
    subst e
    rcases h with ⟨hl,_,hm⟩ | ⟨hr,hl,hm⟩
    · simpa [neighborPosition,hl] using hm
    · have hn : edgeLeft G (neighborEdge G v w) ≠ v := by
        intro heq
        exact (endpoint_adj G (neighborEdge G v w)).ne (heq.trans hr.symm)
      simpa [neighborPosition,hn] using hm

abbrev ActiveNeighbor {v : V} (f : G.neighborSet v → Option (Fin k)) :=
  {w : G.neighborSet v // ∃ b, f w = some b}

def activeLabel {v : V} (f : G.neighborSet v → Option (Fin k)) (w : ActiveNeighbor G f) : Fin k :=
  w.property.choose

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem activeLabel_spec {v : V} (f : G.neighborSet v → Option (Fin k)) (w : ActiveNeighbor G f) :
    f w.val = some (activeLabel G f w) := w.property.choose_spec

def neighborRowPosition {v : V} (f : G.neighborSet v → Option (Fin k))
    (z : Fin k × ActiveNeighbor G f) : G.edgeSet × (Fin k × Fin k) :=
  (neighborEdge G v z.2.val,neighborPosition G v z.2.val z.1 (activeLabel G f z.2))

omit [Fintype V] [DecidableRel G.Adj] in
theorem neighborRowPosition_injective {v : V} (f : G.neighborSet v → Option (Fin k)) :
    Function.Injective (neighborRowPosition G f) := by
  rintro ⟨a,w⟩ ⟨b,z⟩ h
  have he : neighborEdge G v w.val = neighborEdge G v z.val := congrArg Prod.fst h
  have hw : w = z := Subtype.ext ((neighborEdge_injective G v) he)
  subst z
  have hp := congrArg Prod.snd h
  change neighborPosition G v w.val a (activeLabel G f w) =
    neighborPosition G v w.val b (activeLabel G f w) at hp
  unfold neighborPosition at hp
  split_ifs at hp
  · have hab : a = b := congrArg (fun p : Fin k × Fin k => p.1) hp
    exact Prod.ext hab rfl
  · have hab : a = b := congrArg (fun p : Fin k × Fin k => p.2) hp
    exact Prod.ext hab rfl

def neighborRowEmbedding {v : V} (f : G.neighborSet v → Option (Fin k)) :
    (Fin k × ActiveNeighbor G f) ↪ (G.edgeSet × (Fin k × Fin k)) :=
  ⟨neighborRowPosition G f,neighborRowPosition_injective G f⟩

def choiceDominates {v : V} (f : G.neighborSet v → Option (Fin k))
    (M : G.edgeSet → EdgeMatrix k) : Prop :=
  ∀ a, ∃ w : ActiveNeighbor G f,
    M (neighborEdge G v w.val) (neighborPosition G v w.val a (activeLabel G f w)) = true

theorem choice_domination_probability (v : V) (f : G.neighborSet v → Option (Fin k)) :
    (FiniteProb.pi (fun _ : G.edgeSet => FiniteProb.fairBits (Fin k × Fin k))).prob
      (choiceDominates G f) ≤ Real.exp (-(k:ℝ)*(2:ℝ)^(-(G.degree v:ℤ))) := by
  have hc : Fintype.card (ActiveNeighbor G f) ≤ G.degree v := by
    have h := Fintype.card_le_of_injective (fun w : ActiveNeighbor G f => w.val) Subtype.val_injective
    simpa only [G.card_neighborSet_eq_degree] using h
  have h := FiniteProb.fixed_domination_probability (neighborRowEmbedding G f) hc
  have hm := FiniteProb.fairMatrices_map_flat (E := G.edgeSet) k
  have hp := congrArg (fun μ : FiniteProb ((G.edgeSet × (Fin k × Fin k)) → Bool) =>
    μ.prob (fun x => ∀ a, ∃ w : ActiveNeighbor G f, x (neighborRowEmbedding G f (a,w))=true)) hm
  dsimp only at hp
  rw [FiniteProb.prob_map] at hp
  rw [← hp] at h
  simpa only [Fintype.card_fin,neighborRowEmbedding,neighborRowPosition,flatMatrixEquiv,
    Equiv.coe_fn_mk,Function.Embedding.coeFn_mk] using h

omit [Fintype V] [DecidableRel G.Adj] in
theorem external_domination_has_choice (M : G.edgeSet → EdgeMatrix k) (v : V)
    (h : ExternallyDominatable (cliqueBlowup G M) (vertexClique v)) :
    ∃ f : G.neighborSet v → Option (Fin k), choiceDominates G f M := by
  obtain ⟨S,hS,hdis,hdom⟩ := h
  let f : G.neighborSet v → Option (Fin k) := fun w => chooseLabel (fun b => (w.val,b) ∈ S)
  refine ⟨f,fun a => ?_⟩
  obtain ⟨⟨w,b⟩,hwb,hadj⟩ := hdom (v,a) rfl
  have hwv : w ≠ v := by
    intro he
    exact Set.disjoint_left.mp hdis (show (w,b) ∈ vertexClique v from he) hwb
  have hsk : G.Adj v w :=
    (blowup_adj_skeleton G M hadj).resolve_left (Ne.symm hwv)
  let wn : G.neighborSet v := ⟨w,hsk⟩
  have hf : f wn = some b := by
    change chooseLabel (fun c => (w,c) ∈ S) = some b
    unfold chooseLabel
    have hp : ∃ c, (w,c) ∈ S := ⟨b,hwb⟩
    rw [dif_pos hp]
    apply congrArg some
    have heq := clique_independent_at_most_one (cliqueBlowup G M)
      (vertexClique_isClique G M w) hS (show (w,hp.choose) ∈ vertexClique w from rfl)
      hp.choose_spec (show (w,b) ∈ vertexClique w from rfl) hwb
    exact congrArg Prod.snd heq
  let wa : ActiveNeighbor G f := ⟨wn,⟨b,hf⟩⟩
  refine ⟨wa,?_⟩
  have he : activeLabel G f wa = b := Option.some.inj ((activeLabel_spec G f wa).symm.trans hf)
  rw [he]
  exact adjacent_neighbor_entry G M v wn a b hadj

theorem external_domination_probability (v : V) :
    (FiniteProb.pi (fun _ : G.edgeSet => FiniteProb.fairBits (Fin k × Fin k))).prob
      (fun M => ExternallyDominatable (cliqueBlowup G M) (vertexClique v)) ≤
      ((k+1:ℕ):ℝ)^(G.degree v) * Real.exp (-(k:ℝ)*(2:ℝ)^(-(G.degree v:ℤ))) := by
  let μ := FiniteProb.pi (fun _ : G.edgeSet => FiniteProb.fairBits (Fin k × Fin k))
  calc
    _ ≤ μ.prob (fun M => ∃ f : G.neighborSet v → Option (Fin k), choiceDominates G f M) :=
      μ.prob_mono (fun M h => external_domination_has_choice G M v h)
    _ ≤ ∑ f : G.neighborSet v → Option (Fin k), μ.prob (choiceDominates G f) :=
      μ.prob_exists_le_sum _
    _ ≤ ∑ _f : G.neighborSet v → Option (Fin k),
        Real.exp (-(k:ℝ)*(2:ℝ)^(-(G.degree v:ℤ))) :=
      Finset.sum_le_sum (fun f _ => choice_domination_probability G v f)
    _ = _ := by simp [Fintype.card_fun,G.card_neighborSet_eq_degree]

end TreeGeometry
end
end MISLocal
