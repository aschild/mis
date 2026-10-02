import MISLocal.AnonymousRule
import MISLocal.Locality

/-! The actual graph given to a LOCAL algorithm: a clique at each skeleton
vertex, with the cross-clique adjacencies read from its incident matrices.
The stored orientation of a skeleton edge has no graph-theoretic meaning. -/

open scoped Classical
namespace MISLocal
noncomputable section
namespace TreeGeometry

variable {V : Type*} (G : SimpleGraph V) {k : ℕ}

def crossCliqueAdj (M : G.edgeSet → EdgeMatrix k)
    (x y : V × Fin k) : Prop :=
  ∃ e, (edgeLeft G e = x.1 ∧ edgeRight G e = y.1 ∧ M e (x.2,y.2) = true) ∨
    (edgeRight G e = x.1 ∧ edgeLeft G e = y.1 ∧ M e (y.2,x.2) = true)

theorem crossCliqueAdj_symm (M : G.edgeSet → EdgeMatrix k)
    {x y : V × Fin k} (h : crossCliqueAdj G M x y) : crossCliqueAdj G M y x := by
  rcases h with ⟨e,h | h⟩
  · exact ⟨e,Or.inr ⟨h.2.1,h.1,h.2.2⟩⟩
  · exact ⟨e,Or.inl ⟨h.2.1,h.1,h.2.2⟩⟩

theorem crossCliqueAdj_skeleton (M : G.edgeSet → EdgeMatrix k)
    {x y : V × Fin k} (h : crossCliqueAdj G M x y) : G.Adj x.1 y.1 := by
  rcases h with ⟨e,h | h⟩
  · rw [← h.1,← h.2.1]; exact endpoint_adj G e
  · rw [← h.1,← h.2.1]; exact (endpoint_adj G e).symm

def cliqueBlowup (M : G.edgeSet → EdgeMatrix k) : SimpleGraph (V × Fin k) where
  Adj x y := (x.1 = y.1 ∧ x.2 ≠ y.2) ∨ crossCliqueAdj G M x y
  symm := by
    intro x y h
    rcases h with h | h
    · exact Or.inl ⟨h.1.symm,Ne.symm h.2⟩
    · exact Or.inr (crossCliqueAdj_symm G M h)
  loopless := by
    intro x h
    rcases h with h | h
    · exact h.2 rfl
    · exact G.irrefl (crossCliqueAdj_skeleton G M h)

def vertexClique (v : V) : Set (V × Fin k) := {x | x.1 = v}

theorem vertexClique_isClique (M : G.edgeSet → EdgeMatrix k) (v : V) :
    (cliqueBlowup G M).IsClique (vertexClique v) := by
  intro x hx y hy hxy
  apply Or.inl
  refine ⟨hx.trans hy.symm,?_⟩
  intro h
  exact hxy (Prod.ext (hx.trans hy.symm) h)

theorem blowup_adj_skeleton (M : G.edgeSet → EdgeMatrix k)
    {x y : V × Fin k} (h : (cliqueBlowup G M).Adj x y) :
    x.1 = y.1 ∨ G.Adj x.1 y.1 :=
  h.elim (fun h => Or.inl h.1) (fun h => Or.inr (crossCliqueAdj_skeleton G M h))

theorem blowup_ball_skeleton (M : G.edgeSet → EdgeMatrix k) (t : ℕ)
    (x y : V × Fin k) (h : InBall (cliqueBlowup G M) t x y) :
    InBall G t x.1 y.1 := by
  induction t generalizing x y with
  | zero => exact congrArg Prod.fst h
  | succ t ih =>
    rcases h with h | ⟨z,hxz,hzy⟩
    · exact Or.inl (congrArg Prod.fst h)
    · have hz := ih z y hzy
      rcases blowup_adj_skeleton G M hxz with h | h
      · rw [← h] at hz
        exact inBall_mono_succ G t x.1 y.1 hz
      · exact Or.inr ⟨z.1,h,hz⟩

theorem selected_matrix_edge (M : G.edgeSet → EdgeMatrix k) (e : G.edgeSet)
    (a b : Fin k) (h : M e (a,b) = true) :
    (cliqueBlowup G M).Adj (edgeLeft G e,a) (edgeRight G e,b) :=
  Or.inr ⟨e,Or.inl ⟨rfl,rfl,h⟩⟩

theorem repaired_clique_unique (M : G.edgeSet → EdgeMatrix k) (S : Set (V × Fin k))
    (v : V) {a b : Fin k}
    (ha : (v,a) ∈ repair (cliqueBlowup G M) S)
    (hb : (v,b) ∈ repair (cliqueBlowup G M) S) : a = b := by
  have h := clique_independent_at_most_one (cliqueBlowup G M)
    (vertexClique_isClique G M v) (repair_independent _ S)
    (show (v,a) ∈ vertexClique v from rfl) ha
    (show (v,b) ∈ vertexClique v from rfl) hb
  exact congrArg Prod.snd h

def repairedLabel (M : G.edgeSet → EdgeMatrix k) (S : Set (V × Fin k)) (v : V) :
    Option (Fin k) :=
  if h : ∃ a, (v,a) ∈ repair (cliqueBlowup G M) S then some h.choose else none

theorem repairedLabel_some (M : G.edgeSet → EdgeMatrix k) (S : Set (V × Fin k))
    (v : V) (a : Fin k) :
    repairedLabel G M S v = some a ↔ (v,a) ∈ repair (cliqueBlowup G M) S := by
  unfold repairedLabel
  split_ifs with h
  · constructor
    · intro he; exact (Option.some.inj he) ▸ h.choose_spec
    · intro ha
      exact congrArg some (repaired_clique_unique G M S v h.choose_spec ha)
  · simp only [reduceCtorEq, false_iff]
    exact fun ha => h ⟨a,ha⟩

theorem repairedLabel_occupies (M : G.edgeSet → EdgeMatrix k) (S : Set (V × Fin k))
    (v : V) : repairedLabel G M S v ≠ none ↔
      Occupies (vertexClique v) (repair (cliqueBlowup G M) S) := by
  unfold repairedLabel
  split_ifs with h
  · simp only [ne_eq, Option.some_ne_none, not_false_eq_true, true_iff]
    exact ⟨(v,h.choose),rfl,h.choose_spec⟩
  · simp only [ne_eq, not_true_eq_false, false_iff]
    rintro ⟨⟨w,a⟩,hw,ha⟩
    exact h ⟨a,hw ▸ ha⟩

theorem repairedLabel_noConflict (M : G.edgeSet → EdgeMatrix k)
    (S : Set (V × Fin k)) (e : G.edgeSet) :
    ¬selectedConflict (fun M a b => M (a,b)=true)
      (M e,repairedLabel G M S (edgeLeft G e),repairedLabel G M S (edgeRight G e)) := by
  unfold selectedConflict
  generalize hl : repairedLabel G M S (edgeLeft G e) = l
  generalize hr : repairedLabel G M S (edgeRight G e) = r
  cases l with
  | none => simp
  | some a =>
    cases r with
    | none => simp
    | some b =>
      intro hab
      have ha := (repairedLabel_some G M S (edgeLeft G e) a).mp hl
      have hb := (repairedLabel_some G M S (edgeRight G e) b).mp hr
      exact ha.2 _ (selected_matrix_edge G M e a b hab) hb.1

end TreeGeometry
end
end MISLocal
