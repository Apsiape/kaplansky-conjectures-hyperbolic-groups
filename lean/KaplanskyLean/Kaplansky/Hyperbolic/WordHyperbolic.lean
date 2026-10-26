import Kaplansky.Challenge
import OAI.GroupTheory.Hyperbolic.GraphMetric

/-!
# From a linear cochain bound to word-hyperbolicity

The vendored `Release075.Discrete.Path.triangleNear_of_cochainBound` turns a `CochainBound` on a
geodesic metric into uniformly thin geodesic triangles. This file transports that conclusion to
the Challenge definition `Kaplansky.WordHyperbolic` for the Cayley graph `mulCayley S`.
The proof is a copy of Release075's `presentation_wordHyperbolic`, made generic.

It also proves that `WordHyperbolic`, `TorsionFree`, `HasFiniteTwoDimensionalClassifyingSpace`
and hence `GoodHyperbolic` are invariant under group isomorphisms `G ≃* H`
(`wordHyperbolic_of_mulEquiv`, `goodHyperbolic_of_mulEquiv`).
-/

namespace Kaplansky.Hyperbolic

open OAI.Release075

variable {G : Type} [Group G]

/-- A finite connected Cayley graph whose graph metric satisfies a linear cochain bound
gives a word-hyperbolic group, in the literal thin-triangle sense of `Kaplansky.WordHyperbolic`. -/
theorem wordHyperbolic_of_cochainBound (S : Set G) (hS : S.Finite)
    (hX : (SimpleGraph.mulCayley S).Connected) {B : ℕ}
    (hB : Discrete.CochainBound (Discrete.graphMetric (SimpleGraph.mulCayley S) hX) B) :
    Kaplansky.WordHyperbolic G := by
  let X := SimpleGraph.mulCayley S
  refine ⟨S, hS, hX, 10000 * (B + 1), ?_⟩
  intro x y z p q s hp hq hs
  let p' := Discrete.walkPath X hX p
  let q' := Discrete.walkPath X hX q
  let s' := Discrete.walkPath X hX s.reverse
  have hp' : p'.Geodesic := hp
  have hq' : q'.Geodesic := hq
  have hs' : s'.Geodesic := by
    change s.reverse.length = X.dist x z
    rw [SimpleGraph.Walk.length_reverse, X.dist_comm]
    exact hs
  have hthin := Discrete.Path.triangleNear_of_cochainBound
    (Discrete.graphMetric_geodesicSpace X hX) hB hp' hq' hs'
  have hpMem (v : G) : p'.Mem v ↔ v ∈ p.support := Discrete.walkPath_mem X hX p
  have hqMem (v : G) : q'.Mem v ↔ v ∈ q.support := Discrete.walkPath_mem X hX q
  have hsMem (v : G) : s'.Mem v ↔ v ∈ s.support := by
    rw [Discrete.walkPath_mem, SimpleGraph.Walk.support_reverse, List.mem_reverse]
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨w, hw, hd⟩ := hthin.1 v ((hpMem v).mpr hv)
    exact ⟨w, hw.imp ((hqMem w).mp) ((hsMem w).mp), hd⟩
  · intro v hv
    obtain ⟨w, hw, hd⟩ := hthin.2.1 v ((hqMem v).mpr hv)
    exact ⟨w, hw.imp ((hsMem w).mp) ((hpMem w).mp), hd⟩
  · intro v hv
    obtain ⟨w, hw, hd⟩ := hthin.2.2 v ((hsMem v).mpr hv)
    exact ⟨w, hw.imp ((hpMem w).mp) ((hqMem w).mp), hd⟩

/-! ### Transport along group isomorphisms -/

section Transport

/-- Graph isomorphisms of connected graphs do not increase distances. -/
lemma iso_dist_le {V W : Type} {X : SimpleGraph V} {Y : SimpleGraph W} (φ : X ≃g Y)
    (hX : X.Connected) (u v : V) : Y.dist (φ u) (φ v) ≤ X.dist u v := by
  obtain ⟨p, hp⟩ := hX.exists_walk_length_eq_dist u v
  calc Y.dist (φ u) (φ v) ≤ (p.map φ.toHom).length := SimpleGraph.dist_le _
    _ = X.dist u v := by rw [SimpleGraph.Walk.length_map, hp]

/-- Graph isomorphisms of connected graphs preserve distances. -/
lemma iso_dist {V W : Type} {X : SimpleGraph V} {Y : SimpleGraph W} (φ : X ≃g Y)
    (hX : X.Connected) (u v : V) : Y.dist (φ u) (φ v) = X.dist u v := by
  refine le_antisymm (iso_dist_le φ hX u v) ?_
  have h := iso_dist_le φ.symm (φ.connected_iff.mp hX) (φ u) (φ v)
  simpa using h

variable {G H : Type} [Group G] [Group H]

/-- A group isomorphism is a graph isomorphism of Cayley graphs, generators `S ↦ e '' S`. -/
def mulCayleyIso (e : G ≃* H) (S : Set G) :
    SimpleGraph.mulCayley S ≃g SimpleGraph.mulCayley (e '' S) where
  toEquiv := e.toEquiv
  map_rel_iff' {u v} := by
    change (SimpleGraph.mulCayley (e '' S)).Adj (e u) (e v) ↔ (SimpleGraph.mulCayley S).Adj u v
    simp only [SimpleGraph.mulCayley_adj', Set.exists_mem_image, ← map_mul, e.injective.eq_iff,
      ne_eq]

@[simp] lemma mulCayleyIso_apply (e : G ≃* H) (S : Set G) (g : G) : mulCayleyIso e S g = e g :=
  rfl

/-- Word-hyperbolicity (Challenge definition) is invariant under group isomorphism. -/
theorem wordHyperbolic_of_mulEquiv (e : G ≃* H) (h : Kaplansky.WordHyperbolic G) :
    Kaplansky.WordHyperbolic H := by
  obtain ⟨S, hS, hconn, δ, hthin⟩ := h
  let φ := mulCayleyIso e S
  let ψ := φ.symm
  have hconn' : (SimpleGraph.mulCayley (e '' S)).Connected := φ.connected_iff.mp hconn
  have hψ : ∀ a b, (SimpleGraph.mulCayley S).dist (ψ a) (ψ b) =
      (SimpleGraph.mulCayley (e '' S)).dist a b := iso_dist ψ hconn'
  have geo : ∀ {a b : H} (P : (SimpleGraph.mulCayley (e '' S)).Walk a b),
      Kaplansky.Geodesic _ P → Kaplansky.Geodesic _ (P.map ψ.toHom) := by
    intro a b P hP
    unfold Kaplansky.Geodesic at hP ⊢
    rw [SimpleGraph.Walk.length_map, hP]
    exact (hψ a b).symm
  have push : ∀ {a b c : H} (P : (SimpleGraph.mulCayley (e '' S)).Walk a b)
      (Q : (SimpleGraph.mulCayley (e '' S)).Walk b c)
      (R : (SimpleGraph.mulCayley (e '' S)).Walk c a),
      Kaplansky.SideThin _ δ (P.map ψ.toHom) (Q.map ψ.toHom) (R.map ψ.toHom) →
      Kaplansky.SideThin _ δ P Q R := by
    intro a b c P Q R hs v hv
    obtain ⟨w, hw, hd⟩ := hs (ψ v) (by
      rw [SimpleGraph.Walk.support_map]
      exact List.mem_map_of_mem hv)
    refine ⟨φ w, ?_, ?_⟩
    · rw [SimpleGraph.Walk.support_map, SimpleGraph.Walk.support_map] at hw
      rcases hw with hw | hw <;> obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hw
      · left
        simpa [ψ] using hw0
      · right
        simpa [ψ] using hw0
    · rw [← hψ v (φ w)]
      simpa [ψ] using hd
  refine ⟨e '' S, hS.image e, hconn', δ, ?_⟩
  intro x y z p q r hp hq hr
  obtain ⟨h1, h2, h3⟩ := hthin _ _ _ (p.map ψ.toHom) (q.map ψ.toHom) (r.map ψ.toHom)
    (geo p hp) (geo q hq) (geo r hr)
  exact ⟨push p q r h1, push q r p h2, push r p q h3⟩

theorem wordHyperbolic_congr (e : G ≃* H) :
    Kaplansky.WordHyperbolic G ↔ Kaplansky.WordHyperbolic H :=
  ⟨wordHyperbolic_of_mulEquiv e, wordHyperbolic_of_mulEquiv e.symm⟩

theorem torsionFree_transport (e : G ≃* H) (h : Kaplansky.TorsionFree G) :
    Kaplansky.TorsionFree H := by
  intro g n hn hg
  have h1 : e.symm g = 1 := h (e.symm g) n hn (by rw [← map_pow, hg, map_one])
  simpa using congrArg e h1

theorem classifyingSpace_transport (e : G ≃* H)
    (h : Kaplansky.HasFiniteTwoDimensionalClassifyingSpace G) :
    Kaplansky.HasFiniteTwoDimensionalClassifyingSpace H := by
  obtain ⟨X, topX, hT2, hpc, cw, hfin, hdim, hcell, x, ⟨f⟩, hcov⟩ := h
  exact ⟨X, topX, hT2, hpc, cw, hfin, hdim, hcell, x, ⟨e.symm.trans f⟩, hcov⟩

/-- All four geometric hypotheses of the Main Theorem are invariant under group isomorphism. -/
theorem goodHyperbolic_of_mulEquiv (e : G ≃* H) (h : Kaplansky.GoodHyperbolic G) :
    Kaplansky.GoodHyperbolic H := by
  obtain ⟨hfp, htf, hwh, hcs⟩ := h
  exact ⟨Group.IsFinitelyPresented.equiv e, torsionFree_transport e htf,
    wordHyperbolic_of_mulEquiv e hwh, classifyingSpace_transport e hcs⟩

end Transport

end Kaplansky.Hyperbolic
