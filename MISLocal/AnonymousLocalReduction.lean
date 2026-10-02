import MISLocal.ViewSimulation
import MISLocal.IdentifierBits

/-! Construct the anonymous rule from a LOCAL program and a fixed ID-indexed
tape table. A neighborhood collision gate precedes the simulation, and
conflict deletion follows it. Anonymity is obtained by a proved quotient lift. -/

open scoped Classical
namespace MISLocal
noncomputable section

theorem inBall_equiv {V : Type*} (G H : SimpleGraph V) (φ : V ≃ V)
    (h : ∀ v w, H.Adj (φ v) (φ w) ↔ G.Adj v w) (t : ℕ) (v w : V) :
    InBall H t (φ v) (φ w) ↔ InBall G t v w := by
  induction t generalizing v w with
  | zero => exact φ.injective.eq_iff
  | succ t ih =>
    constructor
    · rintro (hw | ⟨z,hvz,hzw⟩)
      · exact Or.inl (φ.injective hw)
      · have hz : H.Adj (φ v) (φ (φ.symm z)) := by simpa using hvz
        have hb : InBall H t (φ (φ.symm z)) (φ w) := by simpa using hzw
        exact Or.inr ⟨φ.symm z,(h v _).mp hz,(ih _ _).mp hb⟩
    · rintro (hw | ⟨z,hvz,hzw⟩)
      · exact Or.inl (congrArg φ hw)
      · exact Or.inr ⟨φ z,(h v z).mpr hvz,(ih z w).mpr hzw⟩

theorem repair_equiv {V : Type*} (G H : SimpleGraph V) (φ : V ≃ V)
    (S S' : Set V) (hG : ∀ v w, H.Adj (φ v) (φ w) ↔ G.Adj v w)
    (hS : ∀ v, φ v ∈ S' ↔ v ∈ S) (v : V) :
    φ v ∈ repair H S' ↔ v ∈ repair G S := by
  constructor
  · rintro ⟨hv,hn⟩
    exact ⟨(hS v).mp hv,fun w hw hsw => hn (φ w) ((hG v w).mpr hw) ((hS w).mpr hsw)⟩
  · rintro ⟨hv,hn⟩
    refine ⟨(hS v).mpr hv,fun w hw hsw => ?_⟩
    have ha : H.Adj (φ v) (φ (φ.symm w)) := by simpa using hw
    have hs : φ (φ.symm w) ∈ S' := by simpa using hsw
    exact hn (φ.symm w) ((hG v _).mp ha) ((hS _).mp hs)

def chooseLabel {k : ℕ} (P : Fin k → Prop) : Option (Fin k) :=
  if h : ∃ a, P a then some h.choose else none

theorem chooseLabel_congr {k : ℕ} {P Q : Fin k → Prop}
    (h : ∀ a, P a ↔ Q a) : chooseLabel P = chooseLabel Q := by
  have he : P = Q := funext (fun a => propext (h a))
  rw [he]

theorem chooseLabel_mem {k : ℕ} {P : Fin k → Prop} {a : Fin k}
    (h : chooseLabel P = some a) : P a := by
  unfold chooseLabel at h
  split_ifs at h with hp
  · exact (Option.some.inj h) ▸ hp.choose_spec

theorem chooseLabel_nonempty {k : ℕ} (P : Fin k → Prop) :
    chooseLabel P ≠ none ↔ ∃ a, P a := by
  unfold chooseLabel
  split_ifs <;> simp_all

variable {V E : Type*} [Fintype V] [Fintype E] {m b : ℕ}
    (pack : (Fin (2*m) × Fin b) ↪ (Fin m × Fin m))

def snapshotIdentifiers (x : NamedLocalView V E (2*m) Unit) :
    (V × Fin (2*m)) → Fin (2^b) := fun va =>
  wordIdentifierEquiv b (fun t => snapshotBlockStrings m x va.1 (pack (va.2,t)))

omit [Fintype V] in
theorem snapshotIdentifiers_rename {x y : NamedLocalView V E (2*m) Unit}
    (φ : V ≃ V) (ψ : E ≃ E) (flip : E → Bool)
    (h : ∀ e, y.edges (ψ e) = (x.edges e).map (renameEdgeDatum φ (flip e)))
    (va : V × Fin (2*m)) :
    snapshotIdentifiers pack y (cliqueVertexRename (2*m) φ va) = snapshotIdentifiers pack x va := by
  change wordIdentifierEquiv b (fun t => snapshotBlockStrings m y (φ va.1) (pack (va.2,t))) = _
  rw [snapshotBlockStrings_rename m φ ψ flip h]
  rfl

def snapshotUnique (T : ℕ) (x : NamedLocalView V E (2*m) Unit) (v : V) : Prop :=
  Set.InjOn (snapshotIdentifiers pack x) {z | InBall (snapshotSkeleton x) (T+1) v z.1}

omit [Fintype V] in
theorem snapshotUnique_rename (T : ℕ) {x y : NamedLocalView V E (2*m) Unit}
    (φ : V ≃ V) (ψ : E ≃ E) (flip : E → Bool)
    (h : ∀ e, y.edges (ψ e) = (x.edges e).map (renameEdgeDatum φ (flip e))) (v : V) :
    snapshotUnique pack T y (φ v) ↔ snapshotUnique pack T x v := by
  let Φ := cliqueVertexRename (2*m) φ
  have hid := snapshotIdentifiers_rename pack φ ψ flip h
  have hb (z : V × Fin (2*m)) :
      InBall (snapshotSkeleton y) (T+1) (φ v) (Φ z).1 ↔
        InBall (snapshotSkeleton x) (T+1) v z.1 :=
    inBall_equiv _ _ φ (snapshotSkeleton_rename φ ψ flip h) (T+1) v z.1
  constructor
  · intro hu z hz w hw he
    have hids : snapshotIdentifiers pack y (Φ z) = snapshotIdentifiers pack y (Φ w) := by
      rw [hid z,hid w]; exact he
    exact Φ.injective (hu ((hb z).mpr hz) ((hb w).mpr hw) hids)
  · intro hu z hz w hw he
    have hzb := (hb (Φ.symm z)).mp (by simpa [Φ] using hz)
    have hwb := (hb (Φ.symm w)).mp (by simpa [Φ] using hw)
    have hids : snapshotIdentifiers pack x (Φ.symm z) = snapshotIdentifiers pack x (Φ.symm w) := by
      rw [← hid (Φ.symm z),← hid (Φ.symm w)]
      simpa [Φ] using he
    exact Φ.symm.injective (hu hzb hwb hids)

variable {Tape State : Type*} (A : UniformLocalProtocol (2^b) Tape State)
    (W : Fin (2^b) → Tape) (T : ℕ)

def snapshotCandidates (x : NamedLocalView V E (2*m) Unit) : Set (V × Fin (2*m)) :=
  {z | snapshotUnique pack T x z.1 ∧
    z ∈ A.candidates (snapshotBlowup x) (snapshotIdentifiers pack x) W T}

theorem snapshotCandidates_rename {x y : NamedLocalView V E (2*m) Unit}
    (φ : V ≃ V) (ψ : E ≃ E) (flip : E → Bool)
    (h : ∀ e, y.edges (ψ e) = (x.edges e).map (renameEdgeDatum φ (flip e)))
    (z : V × Fin (2*m)) :
    cliqueVertexRename (2*m) φ z ∈ snapshotCandidates pack A W T y ↔
      z ∈ snapshotCandidates pack A W T x := by
  apply and_congr (snapshotUnique_rename pack T φ ψ flip h z.1)
  apply Iff.symm
  apply A.candidates_transport _ _ (cliqueVertexRename (2*m) φ)
  · intro u _; exact (snapshotIdentifiers_rename pack φ ψ flip h u).symm
  · intro u _ w; exact (snapshotBlowup_rename φ ψ flip h u w).symm

def snapshotRepairedLabel (x : NamedLocalView V E (2*m) Unit) : Option (Fin (2*m)) :=
  chooseLabel (fun a => (x.root,a) ∈ repair (snapshotBlowup x) (snapshotCandidates pack A W T x))

theorem snapshotRepairedLabel_rename {x y : NamedLocalView V E (2*m) Unit}
    (h : LocalViewRenaming x y) :
    snapshotRepairedLabel pack A W T x = snapshotRepairedLabel pack A W T y := by
  obtain ⟨φ,ψ,flip,hr,_,he⟩ := h
  apply chooseLabel_congr
  intro a
  have hrep := repair_equiv (snapshotBlowup x) (snapshotBlowup y)
    (cliqueVertexRename (2*m) φ) _ _ (snapshotBlowup_rename φ ψ flip he)
    (snapshotCandidates_rename pack A W T φ ψ flip he) (x.root,a)
  simpa only [hr,cliqueVertexRename,Equiv.prodCongr_apply,Equiv.refl_apply,Prod.map] using hrep.symm

def localAnonymousRule : AnonymousRule V E (2*m) Unit :=
  Quot.lift (snapshotRepairedLabel pack A W T) (fun _ _ h =>
    snapshotRepairedLabel_rename pack A W T h)

end
end MISLocal
