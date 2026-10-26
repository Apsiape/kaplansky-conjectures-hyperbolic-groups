import OAI.GroupTheory.Hyperbolic.ThinTriangles

/-!
Source: OpenAI, openai/math, commit
1581d4cbdd69a0faf34b2089614fe2a814316a6a,
lean/OAI/GroupTheory/Hyperbolic/CayleyMetric.lean.
Licensed under Apache-2.0; see OAI/LICENSE-APACHE-2.0-OpenAI.
Modified for KaplanskyLean: this file retains upstream lines 1-39,
the generic graph metric, followed by the closing "end OAI";
the remaining upstream material was omitted, and this notice was added.
-/

namespace OAI

namespace Release075.Discrete
variable {V : Type} (X : SimpleGraph V) (hX : X.Connected)

noncomputable def graphMetric : Metric V where
  dist := X.dist
  self _ := X.dist_self
  symm _ _ := X.dist_comm
  triangle _ _ _ := hX.dist_triangle

noncomputable def walkPath {a b : V} (p : X.Walk a b) : Path (graphMetric X hX) a b where
  length := p.length
  point := p.getVert
  zero := p.getVert_zero
  stable _ h := p.getVert_of_length_le h
  step _ h := by
    change X.dist _ _ ≤ 1
    exact (X.dist_eq_one_iff_adj.mpr (p.adj_getVert_succ h)).le

@[simp] theorem walkPath_mem {a b x : V} (p : X.Walk a b) :
    (walkPath X hX p).Mem x ↔ x ∈ p.support := by
  classical
  constructor
  · rintro ⟨i,_,rfl⟩
    exact p.getVert_mem_support i
  · intro hx
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hx
    refine ⟨i,by change i ≤ p.length; rw [p.length_support] at hi; omega,?_⟩
    exact (p.getVert_eq_support_getElem (by rw [p.length_support] at hi; omega)).trans he

theorem graphMetric_geodesicSpace : GeodesicSpace (graphMetric X hX) := by
  intro a b
  obtain ⟨p,hp⟩ := hX.exists_walk_length_eq_dist a b
  exact ⟨walkPath X hX p,hp⟩

end Release075.Discrete

end OAI
