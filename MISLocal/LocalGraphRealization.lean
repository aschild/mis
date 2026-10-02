import MISLocal.EmbeddedLocalExecution
import MISLocal.BlowupIDCompletion
/-! Realize a local neighborhood on exactly n legal identifiers, padding with isolated vertices. -/
open scoped Classical
namespace MISLocal
noncomputable section
def localIDEmbedding {X : Type*} [Fintype X] {n : ℕ} (U : Set X)
    (ids : X → Fin n) (hn : Fintype.card U ≤ n) : U ↪ Fin n :=
  if h : Set.InjOn ids U then
    ⟨fun u => ids u.val,fun u v huv => Subtype.ext (h u.property v.property huv)⟩
  else Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa only [Fintype.card_fin] using hn))
theorem localIDEmbedding_agrees {X : Type*} [Fintype X] {n : ℕ} (U : Set X)
    (ids : X → Fin n) (hn : Fintype.card U ≤ n) (hi : Set.InjOn ids U) (u : U) :
    localIDEmbedding U ids hn u = ids u.val := by
  simp only [localIDEmbedding,dif_pos hi,Function.Embedding.coeFn_mk]
def localRealization {X : Type*} [Fintype X] {n : ℕ} (H : SimpleGraph X)
    (U : Set X) (ids : X → Fin n) (hn : Fintype.card U ≤ n) : SimpleGraph (Fin n) :=
  (H.induce U).map (localIDEmbedding U ids hn)
namespace UniformLocalProtocol
variable {n : ℕ} {Tape State X : Type*} [Fintype X]
theorem run_map (A : UniformLocalProtocol n Tape State) (G : SimpleGraph X)
    (φ : X ↪ Fin n) (ids : X → Fin n) (W : Fin n → Tape) (t : ℕ) (v : X)
    (hi : ∀ u, ids u = φ u) : A.run G ids W t v = A.run (G.map φ) id W t (φ v) := by
  apply A.run_embedding G (G.map φ) φ ids id W t v
  · exact fun u _ => hi u
  · exact fun _ _ _ => SimpleGraph.map_adj_apply.symm
  · intro u _ w hw
    obtain ⟨a,b,_,_,hb⟩ := hw
    exact ⟨b,hb⟩
theorem candidates_realization (A : UniformLocalProtocol n Tape State)
    (H : SimpleGraph X) (U : Set X) (ids : X → Fin n) (hn : Fintype.card U ≤ n)
    (W : Fin n → Tape) (t : ℕ) (z : U) (hi : Set.InjOn ids U)
    (hball : ∀ w, InBall H (t+1) z.val w → w ∈ U) :
    z.val ∈ A.candidates H ids W t ↔ localIDEmbedding U ids hn z ∈
      A.candidates (localRealization H U ids hn) id W t := by
  have he := (A.run_induce H U ids W t z hball).symm.trans
    (A.run_map (H.induce U) (localIDEmbedding U ids hn) (fun u => ids u.val)
      W t z (localIDEmbedding_agrees U ids hn hi · |>.symm))
  simp only [candidates,Set.mem_setOf_eq,localRealization,localIDEmbedding_agrees U ids hn hi,he,id_eq]
end UniformLocalProtocol
theorem realization_forces_repaired_occupancy {n : ℕ} {Tape State X : Type*} [Fintype X]
    (A : UniformLocalProtocol n Tape State) (H : SimpleGraph X) (C U : Set X)
    (ids : X → Fin n) (hn : Fintype.card U ≤ n) (W : Fin n → Tape) (T : ℕ)
    (candidates : Set X) (hi : Set.InjOn ids U) (hno : ¬ExternallyDominatable H C)
    (hlocal : ∀ v ∈ C, ∀ z, z = v ∨ H.Adj v z → z ∈ U ∧
      (∀ w, InBall H (T+1) z w → w ∈ U) ∧ (z ∈ candidates ↔ z ∈ A.candidates H ids W T))
    (hcorrect : Maximal (localRealization H U ids hn).IsIndepSet
      (A.candidates (localRealization H U ids hn) id W T)) : Occupies C (repair H candidates) := by
  let φ := localIDEmbedding U ids hn
  let K := localRealization H U ids hn
  let out := A.candidates K id W T
  let S : Set X := {x | ∃ u : U, u.val = x ∧ φ u ∈ out}
  have hind : H.IsIndepSet S := by
    rintro x ⟨u,rfl,hu⟩ y ⟨v,rfl,hv⟩ hxy hAdj
    have ha : K.Adj (φ u) (φ v) := ⟨u,v,hAdj,rfl,rfl⟩
    exact hcorrect.1 hu hv ha.ne ha
  have hsim : ∀ v ∈ C, ∀ z, z = v ∨ H.Adj v z → (z ∈ candidates ↔ z ∈ S) := by
    intro v hv z hz
    obtain ⟨hzu,hball,hcand⟩ := hlocal v hv z hz
    let zu : U := ⟨z,hzu⟩
    have hrun := A.candidates_realization H U ids hn W T zu hi hball
    constructor
    · intro hs; exact ⟨zu,rfl,hrun.mp (hcand.mp hs)⟩
    · rintro ⟨u,hu,hs⟩
      have he : u = zu := Subtype.ext hu
      subst u
      exact hcand.mpr (hrun.mpr hs)
  have hoc : Occupies C S := by
    by_contra hnocc
    apply hno
    refine ⟨S,hind,Set.disjoint_left.mpr (fun x hx hs => hnocc ⟨x,hx,hs⟩),?_⟩
    intro v hv
    have hvu := (hlocal v hv v (Or.inl rfl)).1
    let vu : U := ⟨v,hvu⟩
    have hvnot : φ vu ∉ out := fun hs => hnocc ⟨v,hv,vu,rfl,hs⟩
    obtain ⟨w,hw,hvw⟩ := maximal_independent_dominates K hcorrect hvnot
    obtain ⟨a,b,hab,ha,hb⟩ := hvw
    have hav : a = vu := φ.injective ha
    subst a
    exact ⟨b.val,⟨b,rfl,hb ▸ hw⟩,hab⟩
  exact (repair_occupancy_agrees H hind hsim).mpr hoc
end
end MISLocal
