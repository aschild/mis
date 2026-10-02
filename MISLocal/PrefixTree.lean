import MISLocal.GraphBalls
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.Finset.Max

/-! Acyclicity from height and a unique lower neighbor, applied to prefix trees. -/
open scoped Classical
namespace MISLocal
noncomputable section
theorem acyclic_of_unique_lower_neighbor {V : Type*} (G : SimpleGraph V)
    (height : V → ℕ)
    (hstep : ∀ {v w}, G.Adj v w → height v + 1 = height w ∨ height w + 1 = height v)
    (hparent : ∀ {v x y}, G.Adj v x → G.Adj v y →
      height x < height v → height y < height v → x = y) : G.IsAcyclic := by
  intro v p hp
  obtain ⟨z,hz,hmax⟩ := p.support.toFinset.exists_max_image height ⟨v,by simp⟩
  have hz' : z ∈ p.support := List.mem_toFinset.mp hz
  let q := p.rotate hz'
  have hq : q.IsCycle := hp.rotate hz'
  have hbound (u : V) (hu : u ∈ q.support) : height u ≤ height z := by
    have hu' : u ∈ p.support := by
      have hsub := p.toSubgraph_rotate hz'
      have hmem : u ∈ q.toSubgraph.verts := by simpa using hu
      have hpvert : u ∈ p.toSubgraph.verts := by rw [← hsub]; exact hmem
      simpa using hpvert
    exact hmax u (List.mem_toFinset.mpr hu')
  have hs := hstep (SimpleGraph.Walk.adj_snd hq.not_nil)
  have ht := hstep (SimpleGraph.Walk.adj_penultimate hq.not_nil).symm
  have hsl : height q.snd < height z := by
    have := hbound q.snd (q.getVert_mem_support 1)
    rcases hs with hs | hs <;> omega
  have htl : height q.penultimate < height z := by
    have := hbound q.penultimate (q.getVert_mem_support (q.length-1))
    rcases ht with ht | ht <;> omega
  exact hq.snd_ne_penultimate
    (hparent (SimpleGraph.Walk.adj_snd hq.not_nil)
      (SimpleGraph.Walk.adj_penultimate hq.not_nil).symm hsl htl)
def prefixTree (α : Type*) : SimpleGraph (List α) where
  Adj v w := (∃ i, v = i::w) ∨ (∃ i, w = i::v)
  symm := by intro v w h; exact h.symm
  loopless := by
    intro w h
    rcases h with ⟨i,h⟩ | ⟨i,h⟩ <;>
      have he := congrArg List.length h <;> simp only [List.length_cons] at he <;> omega
theorem prefixTree_acyclic (α : Type*) : (prefixTree α).IsAcyclic := by
  apply acyclic_of_unique_lower_neighbor _ List.length
  · rintro v w (⟨i,rfl⟩ | ⟨i,rfl⟩)
    · exact Or.inr rfl
    · exact Or.inl rfl
  · rintro v x y hx hy hxl hyl
    rcases hx with ⟨i,hx⟩ | ⟨i,hx⟩
    · rcases hy with ⟨j,hy⟩ | ⟨j,hy⟩
      · exact (List.cons.inj (hx.symm.trans hy)).2
      · have he := congrArg List.length hy
        simp only [List.length_cons] at he
        omega
    · have he := congrArg List.length hx
      simp only [List.length_cons] at he
      omega
end
end MISLocal
