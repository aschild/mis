import MISLocal.UniformLocalProtocol
import MISLocal.SnapshotAgreement
/-! Transport local execution along an embedding with closed incident rows. -/
open scoped Classical
namespace MISLocal
noncomputable section
theorem inBall_hom {X Y : Type*} (G : SimpleGraph X) (H : SimpleGraph Y)
    (f : G →g H) (t : ℕ) {v w : X} (h : InBall G t v w) : InBall H t (f v) (f w) := by
  induction t generalizing v w with
  | zero => exact congrArg f h
  | succ t ih =>
    rcases h with h | ⟨u,hvu,huw⟩
    · exact Or.inl (congrArg f h)
    · exact Or.inr ⟨f u,f.map_adj hvu,ih huw⟩
namespace UniformLocalProtocol
variable {n : ℕ} {Tape State X Y B : Type*} [Fintype X] [Fintype Y]
theorem neighborImage_embedding [DecidableEq B] (G : SimpleGraph X) (H : SimpleGraph Y)
    (φ : X → Y) (v : X) (f : X → B) (g : Y → B)
    (hrow : ∀ u, G.Adj v u ↔ H.Adj (φ v) (φ u))
    (hclosed : ∀ u, H.Adj (φ v) u → ∃ w, φ w = u)
    (hdata : ∀ u, G.Adj v u → f u = g (φ u)) :
    (Finset.univ.filter (G.Adj v)).image f = (Finset.univ.filter (H.Adj (φ v))).image g := by
  ext z
  constructor
  · intro hz
    obtain ⟨u,hu,huz⟩ := Finset.mem_image.mp hz
    have ha := (Finset.mem_filter.mp hu).2
    exact Finset.mem_image.mpr ⟨φ u,Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,(hrow u).mp ha⟩,(hdata u ha).symm.trans huz⟩
  · intro hz
    obtain ⟨u,hu,huz⟩ := Finset.mem_image.mp hz
    have ha := (Finset.mem_filter.mp hu).2
    obtain ⟨w,rfl⟩ := hclosed u ha
    have haw := (hrow w).mpr ha
    exact Finset.mem_image.mpr ⟨w,Finset.mem_filter.mpr ⟨Finset.mem_univ _,haw⟩,(hdata w haw).trans huz⟩
theorem run_embedding (A : UniformLocalProtocol n Tape State)
    (G : SimpleGraph X) (H : SimpleGraph Y) (φ : X → Y)
    (ids : X → Fin n) (ids' : Y → Fin n) (W : Fin n → Tape) (t : ℕ) (v : X)
    (hids : ∀ u, InBall G (t+1) v u → ids u = ids' (φ u))
    (hrows : ∀ u, InBall G t v u → ∀ w, G.Adj u w ↔ H.Adj (φ u) (φ w))
    (hclosed : ∀ u, InBall G t v u → ∀ w, H.Adj (φ u) w → ∃ z, φ z = w) :
    A.run G ids W t v = A.run H ids' W t (φ v) := by
  induction t generalizing v with
  | zero =>
    have hv := hids v (inBall_self G 1 v)
    have hn : neighbors G ids v = neighbors H ids' (φ v) :=
      neighborImage_embedding G H φ v ids ids' (hrows v rfl) (hclosed v rfl)
        (fun u hu => hids u (Or.inr ⟨u,hu,rfl⟩))
    simp only [run,hv,hn]
  | succ t ih =>
    have hv := hids v (inBall_self G (t+1+1) v)
    have hr := hrows v (inBall_self G (t+1) v)
    have hc := hclosed v (inBall_self G (t+1) v)
    have hs := ih v
      (fun u hu => hids u (inBall_mono_succ G (t+1) v u hu))
      (fun u hu => hrows u (inBall_mono_succ G t v u hu))
      (fun u hu => hclosed u (inBall_mono_succ G t v u hu))
    have hn : (Finset.univ.filter (G.Adj v)).image (fun u => (ids u,A.run G ids W t u)) =
        (Finset.univ.filter (H.Adj (φ v))).image (fun u => (ids' u,A.run H ids' W t u)) := by
      apply neighborImage_embedding G H φ v _ _ hr hc
      intro u hu
      refine Prod.ext (hids u (Or.inr ⟨u,hu,inBall_self G (t+1) u⟩)) ?_
      exact ih u (fun w hw => hids w (Or.inr ⟨u,hu,hw⟩))
        (fun w hw => hrows w (Or.inr ⟨u,hu,hw⟩)) (fun w hw => hclosed w (Or.inr ⟨u,hu,hw⟩))
    simp only [run,hv,hs,hn]
theorem run_induce (A : UniformLocalProtocol n Tape State) (G : SimpleGraph X)
    (U : Set X) (ids : X → Fin n) (W : Fin n → Tape) (t : ℕ) (v : U)
    (hball : ∀ w, InBall G (t+1) v.val w → w ∈ U) :
    A.run (G.induce U) (fun w => ids w.val) W t v = A.run G ids W t v.val := by
  apply A.run_embedding (G.induce U) G Subtype.val _ _ W t v
  · exact fun _ _ => rfl
  · exact fun _ _ _ => Iff.rfl
  · intro u hu w huw
    let inclusion : (G.induce U) →g G := ⟨Subtype.val,fun h => h⟩
    have hb : InBall G t v.val u.val := inBall_hom _ _ inclusion t hu
    exact ⟨⟨w,hball w (inBall_append G t hb huw)⟩,rfl⟩
end UniformLocalProtocol
end
end MISLocal
