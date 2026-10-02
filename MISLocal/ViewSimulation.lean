import MISLocal.DirectedIdentifiers
import MISLocal.UniformLocalProtocol

/-! A concrete LOCAL simulation on a named edge snapshot. Every definition
also makes sense on malformed snapshots, permitting an actual `Quot.lift`
to the anonymous input type. Equivariance is proved pointwise. -/

open scoped BigOperators Classical
namespace MISLocal
noncomputable section

abbrev EdgeDatum (V : Type*) (k : ℕ) := V × V × EdgeMatrix k

def datumSkeleton {V : Type*} {k : ℕ} (z : EdgeDatum V k) (v w : V) : Prop :=
  (z.1 = v ∧ z.2.1 = w) ∨ (z.2.1 = v ∧ z.1 = w)

def datumCross {V : Type*} {k : ℕ} (z : EdgeDatum V k)
    (x y : V × Fin k) : Prop :=
  (z.1 = x.1 ∧ z.2.1 = y.1 ∧ z.2.2 (x.2,y.2) = true) ∨
    (z.2.1 = x.1 ∧ z.1 = y.1 ∧ z.2.2 (y.2,x.2) = true)

theorem datumSkeleton_rename {V : Type*} {k : ℕ} (φ : V ≃ V) (b : Bool)
    (z : EdgeDatum V k) (v w : V) :
    datumSkeleton (renameEdgeDatum φ b z) (φ v) (φ w) ↔ datumSkeleton z v w := by
  cases b <;> simp [datumSkeleton,renameEdgeDatum,or_comm,and_comm]

theorem datumCross_rename {V : Type*} {k : ℕ} (φ : V ≃ V) (b : Bool)
    (z : EdgeDatum V k) (x y : V × Fin k) :
    datumCross (renameEdgeDatum φ b z) (φ x.1,x.2) (φ y.1,y.2) ↔ datumCross z x y := by
  cases b <;> simp [datumCross,renameEdgeDatum,transposeMatrix,or_comm]

def hasDatum {V E : Type*} {k : ℕ} {Q : Type*}
    (x : NamedLocalView V E k Q) (P : EdgeDatum V k → Prop) : Prop :=
  ∃ e, ∃ z, x.edges e = some z ∧ P z

theorem hasDatum_rename {V E : Type*} {k : ℕ} {Q : Type*}
    {x y : NamedLocalView V E k Q} (φ : V ≃ V) (ψ : E ≃ E) (flip : E → Bool)
    (h : ∀ e, y.edges (ψ e) = (x.edges e).map (renameEdgeDatum φ (flip e)))
    (P P' : EdgeDatum V k → Prop)
    (hP : ∀ e z, P' (renameEdgeDatum φ (flip e) z) ↔ P z) :
    hasDatum y P' ↔ hasDatum x P := by
  have he (e : E) : (∃ z, y.edges (ψ e) = some z ∧ P' z) ↔
      ∃ z, x.edges e = some z ∧ P z := by
    rw [h e]
    cases hx : x.edges e with
    | none => simp
    | some z => simpa using hP e z
  constructor
  · rintro ⟨e,hz⟩
    refine ⟨ψ.symm e,(he (ψ.symm e)).mp ?_⟩
    simpa only [ψ.apply_symm_apply] using hz
  · rintro ⟨e,hz⟩
    exact ⟨ψ e,(he e).mpr hz⟩

def snapshotSkeleton {V E : Type*} {k : ℕ} {Q : Type*}
    (x : NamedLocalView V E k Q) : SimpleGraph V where
  Adj v w := v ≠ w ∧ hasDatum x (fun z => datumSkeleton z v w)
  symm := by
    rintro v w ⟨hne,e,z,he,hz⟩
    refine ⟨hne.symm,e,z,he,?_⟩
    exact hz.elim (fun h => Or.inr ⟨h.2,h.1⟩) (fun h => Or.inl ⟨h.2,h.1⟩)
  loopless := fun _ h => h.1 rfl

def snapshotBlowup {V E : Type*} {k : ℕ} {Q : Type*}
    (x : NamedLocalView V E k Q) : SimpleGraph (V × Fin k) where
  Adj v w := (v.1 = w.1 ∧ v.2 ≠ w.2) ∨
    (v.1 ≠ w.1 ∧ hasDatum x (fun z => datumCross z v w))
  symm := by
    rintro v w (h | ⟨hne,e,z,he,hz⟩)
    · exact Or.inl ⟨h.1.symm,h.2.symm⟩
    · refine Or.inr ⟨hne.symm,e,z,he,?_⟩
      exact hz.elim (fun h => Or.inr ⟨h.2.1,h.1,h.2.2⟩)
        (fun h => Or.inl ⟨h.2.1,h.1,h.2.2⟩)
  loopless := by
    intro v h
    rcases h with h | h
    · exact h.2 rfl
    · exact h.1 rfl

def cliqueVertexRename {V : Type*} (k : ℕ) (φ : V ≃ V) :
    (V × Fin k) ≃ (V × Fin k) := Equiv.prodCongr φ (Equiv.refl _)

theorem snapshotSkeleton_rename {V E : Type*} {k : ℕ} {Q : Type*}
    {x y : NamedLocalView V E k Q} (φ : V ≃ V) (ψ : E ≃ E) (flip : E → Bool)
    (h : ∀ e, y.edges (ψ e) = (x.edges e).map (renameEdgeDatum φ (flip e))) (v w : V) :
    (snapshotSkeleton y).Adj (φ v) (φ w) ↔ (snapshotSkeleton x).Adj v w := by
  change (_ ∧ _) ↔ (_ ∧ _)
  rw [φ.injective.ne_iff]
  exact and_congr_right (fun _ => hasDatum_rename φ ψ flip h _ _
    (fun e z => datumSkeleton_rename φ (flip e) z v w))

theorem snapshotBlowup_rename {V E : Type*} {k : ℕ} {Q : Type*}
    {x y : NamedLocalView V E k Q} (φ : V ≃ V) (ψ : E ≃ E) (flip : E → Bool)
    (h : ∀ e, y.edges (ψ e) = (x.edges e).map (renameEdgeDatum φ (flip e)))
    (v w : V × Fin k) :
    (snapshotBlowup y).Adj (cliqueVertexRename k φ v) (cliqueVertexRename k φ w) ↔
      (snapshotBlowup x).Adj v w := by
  change ((φ v.1 = φ w.1 ∧ v.2 ≠ w.2) ∨
    (φ v.1 ≠ φ w.1 ∧ hasDatum y (fun z => datumCross z (φ v.1,v.2) (φ w.1,w.2)))) ↔ _
  simp only [φ.injective.eq_iff,φ.injective.ne_iff]
  exact or_congr Iff.rfl (and_congr_right (fun _ => hasDatum_rename φ ψ flip h _ _
    (fun e z => datumCross_rename φ (flip e) z v w)))

def datumBlockString {V : Type*} (m : ℕ) (v : V) (z : EdgeDatum V (2*m)) :
    Fin m × Fin m → ZMod 2 := fun p =>
  (if z.1 = v then bitGroupEquiv (z.2.2 (directedBlockPosition m (false,p))) else 0) +
    (if z.2.1 = v then bitGroupEquiv (z.2.2 (directedBlockPosition m (true,p))) else 0)

theorem datumBlockString_rename {V : Type*} (m : ℕ) (φ : V ≃ V) (b : Bool)
    (v : V) (z : EdgeDatum V (2*m)) :
    datumBlockString m (φ v) (renameEdgeDatum φ b z) = datumBlockString m v z := by
  funext p
  cases b <;> simp [datumBlockString,renameEdgeDatum,transposeMatrix,
    directedBlockPosition,add_comm]

def snapshotBlockStrings {V E : Type*} [Fintype E] (m : ℕ) {Q : Type*}
    (x : NamedLocalView V E (2*m) Q) (v : V) : Fin m × Fin m → ZMod 2 :=
  ∑ e, (x.edges e).elim 0 (datumBlockString m v)

theorem snapshotBlockStrings_rename {V E : Type*} [Fintype E] (m : ℕ) {Q : Type*}
    {x y : NamedLocalView V E (2*m) Q} (φ : V ≃ V) (ψ : E ≃ E) (flip : E → Bool)
    (h : ∀ e, y.edges (ψ e) = (x.edges e).map (renameEdgeDatum φ (flip e))) (v : V) :
    snapshotBlockStrings m y (φ v) = snapshotBlockStrings m x v := by
  unfold snapshotBlockStrings
  rw [← ψ.sum_comp (fun e => (y.edges e).elim 0 (datumBlockString m (φ v)))]
  apply Finset.sum_congr rfl
  intro e _
  rw [h e]
  cases x.edges e with
  | none => rfl
  | some z => exact datumBlockString_rename m φ (flip e) v z

end
end MISLocal
