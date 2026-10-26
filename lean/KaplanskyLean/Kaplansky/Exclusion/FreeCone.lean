import Kaplansky.Exclusion.Free
import Kaplansky.Hyperbolic.Stokes
import OAI.Algebra.GroupRing.FramedConjugators
import OAI.Algebra.GroupRing.FramedSpherical
import OAI.Algebra.GroupRing.Path

/-!
# Hyperbolicity of the cone group of a pattern-free graph

For a pattern-free graph `Γ` with signed labels `label : D → S₀ × Bool` and routes `R`, the group
`G = GraphPresentation.Group Γ (roseLabel label) R` (the fundamental group of the cone complex,
paper equation (3.1)) is word-hyperbolic.

* `exists_capped`: a null word `u` has a lifted capped picture, built from a free identity among
  conjugates of the route relators (OpenAI's `expansion`, `WordFrames.of_identity`, `Data.strip`,
  `FramedSpherical.spherical`);
* `coneDecomposition`: a reduced capped picture gives a cone decomposition of `u`
  (charge cancellation across arcs, `Lift.pair`);
* `wordHyperbolic_of_patternFree`: with `Capped.cone_bound` (Proposition 4.4, free case) and
  `Hyperbolic.wordHyperbolic_of_cones`.
-/

namespace Kaplansky.Exclusion

open OAI.TorsionFreeZeroDivisors
open PortSubdivision PermutationCycles

section Cone
variable {V D S₀ : Type} [Fintype V] [Fintype D]
  (Γ : PortGraph V D) (label : D → S₀ × Bool)
  (hl : ∀ d, label (Γ.reverse d) = WordPairing.inverseLetter (label d))
  (R : GraphPresentation.Routes Γ)

/-- The cone group. -/
abbrev ConeGroup := GraphPresentation.Group Γ (GraphPresentation.roseLabel label) R

/-- Its generators. -/
def gen : S₀ → ConeGroup Γ label R := PresentedGroup.of

variable {Γ label R}

lemma eval_mk (x : S₀ × Bool) :
    Hyperbolic.eval (gen Γ label R) x = PresentedGroup.mk _ (FreeGroup.mk [x]) := by
  rcases x with ⟨s, b⟩
  cases b
  · simp only [Hyperbolic.eval, gen, Bool.false_eq_true, ite_false]
    change (PresentedGroup.mk _ (FreeGroup.of s))⁻¹ = _
    rw [← map_inv, FreeGroup.of, FreeGroup.inv_mk]
    rfl
  · simp only [Hyperbolic.eval, gen, ite_true]
    rfl

lemma value_mk (w : List (S₀ × Bool)) :
    Hyperbolic.value (gen Γ label R) w = PresentedGroup.mk _ (FreeGroup.mk w) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [Hyperbolic.value_cons, ih, eval_mk, ← map_mul, FreeGroup.mul_mk]
    rfl

lemma heval (x : S₀ × Bool) :
    Hyperbolic.eval (gen Γ label R) (WordPairing.inverseLetter x) =
      (Hyperbolic.eval (gen Γ label R) x)⁻¹ :=
  Hyperbolic.eval_flip _ x

lemma letter_eq (d : D) :
    GraphPresentation.letter Γ (GraphPresentation.roseLabel label) R d =
      Hyperbolic.eval (gen Γ label R) (label d) := by
  rw [eval_mk]; rfl

lemma value_route (v : V) :
    GraphPresentation.value Γ (GraphPresentation.roseLabel label) R v =
      Hyperbolic.value (gen Γ label R) ((R.path v).darts.map label) := by
  rw [value_mk]
  change PresentedGroup.mk _ ((R.path v).eval (GraphPresentation.roseLabel label)) = _
  congr 1
  exact (GraphPresentation.Path.letters_mk label (R.path v)).symm

variable (R) in
/-- The maximal route length. -/
def routeBound : ℕ := Finset.univ.sup (fun v => (R.path v).darts.length)

lemma route_le (v : V) : (R.path v).darts.length ≤ routeBound R :=
  Finset.le_sup (f := fun v => (R.path v).darts.length) (Finset.mem_univ v)

/-! ### The initial capped picture -/

/-- A list of darts with consecutive joins and closing join is the dart list of a closed path. -/
lemma exists_closed_path {V' D' : Type} (Γ' : PortGraph V' D') :
    ∀ (l : List D') (a : V'), (∀ d ∈ l.head?, Γ'.origin d = a) →
      l.IsChain (fun d e => Γ'.origin (Γ'.reverse d) = Γ'.origin e) →
      ∃ b, ∃ p : GraphPresentation.Path Γ' a b, p.darts = l ∧
        (l = [] → b = a) ∧ ∀ d ∈ l.getLast?, Γ'.origin (Γ'.reverse d) = b := by
  intro l
  induction l with
  | nil => intro a _ _; exact ⟨a, .nil a, rfl, fun _ => rfl, by simp⟩
  | cons d l ih =>
    intro a ha hc
    have hd : Γ'.origin d = a := ha d (by simp)
    subst hd
    have hc' := List.isChain_cons.mp hc
    obtain ⟨b, p, hp, hnil, hlast⟩ := ih (Γ'.origin (Γ'.reverse d))
      (fun e he => (hc'.1 e he).symm) hc'.2
    refine ⟨b, .cons d p, by simp [hp], by simp, ?_⟩
    intro e he
    cases l with
    | nil =>
      simp only [List.getLast?_singleton, Option.mem_some_iff] at he
      subst he
      exact (hnil rfl).symm
    | cons f l =>
      exact hlast e (by simpa using he)

/-- The outer darts of the cycle reading `u`. -/
def outerDarts (u : List (S₀ × Bool)) : List (D ⊕ (Fin u.length × Bool)) :=
  List.ofFn (fun i : Fin u.length => Sum.inr (i, true))

lemma outerDarts_labels (u : List (S₀ × Bool)) :
    (outerDarts (D := D) u).map (plusLabel label u) = u := by
  simp only [outerDarts, List.map_ofFn]
  conv_rhs => rw [← List.ofFn_get u]
  rfl

lemma outerDarts_closed (u : List (S₀ × Bool)) (hn : u ≠ []) :
    ∃ v, ∃ p : GraphPresentation.Path (plusGraph Γ u) v v, p.darts = outerDarts u := by
  have hpos : 0 < u.length := List.length_pos_iff.mpr hn
  let a : V ⊕ Fin u.length := Sum.inr ⟨0, hpos⟩
  have hne : outerDarts (D := D) u ≠ [] := by
    simp [outerDarts, List.ofFn_eq_nil_iff, hpos.ne']
  obtain ⟨b, p, hp, -, hlast⟩ := exists_closed_path (plusGraph Γ u) (outerDarts u) a
    (by
      intro d hd
      rw [List.head?_eq_some_head hne, Option.mem_some_iff] at hd
      subst hd
      simp [outerDarts, List.head_ofFn, plusGraph, SumPort.graph, cycleGraph, a])
    (by
      rw [List.isChain_iff_getElem]
      intro i hi
      simp only [outerDarts, List.length_ofFn] at hi
      simp only [outerDarts, List.getElem_ofFn, plusGraph, SumPort.graph, cycleGraph,
        Sum.map_inr, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
      congr 1
      exact Fin.ext (finRotate_val_succ _ hi))
  have hb : b = a := by
    rw [← hlast ((outerDarts u).getLast hne) (List.getLast_mem_getLast? hne)]
    simp only [outerDarts, List.getLast_ofFn, plusGraph, SumPort.graph, cycleGraph,
      Sum.map_inr, Bool.not_true, Bool.false_eq_true, ite_false, a]
    congr 1
    exact Fin.ext (finRotate_val_last _ (by simp; omega))
  subst hb
  exact ⟨a, p, hp⟩

/-- Paths of `Γ` are paths of `Γ⁺`. -/
def mapInl {u : List (S₀ × Bool)} : {a b : V} → GraphPresentation.Path Γ a b →
    GraphPresentation.Path (plusGraph Γ u) (Sum.inl a) (Sum.inl b)
  | _, _, .nil v => .nil _
  | _, _, .cons d p => .cons (Sum.inl d) (mapInl p)

lemma mapInl_darts {u : List (S₀ × Bool)} {a b : V} (p : GraphPresentation.Path Γ a b) :
    (mapInl (u := u) p).darts = p.darts.map Sum.inl := by
  induction p with
  | nil v => rfl
  | cons d p ih =>
    show Sum.inl d :: (mapInl p).darts = (d :: p.darts).map Sum.inl
    rw [ih, List.map_cons]

variable (R) in
include hl in
/-- **The initial capped picture**: every null word has a lifted capped picture. -/
theorem exists_capped (u : List (S₀ × Bool)) (hn : u ≠ [])
    (hu1 : Hyperbolic.value (gen Γ label R) u = 1) :
    ∃ (O : Type) (_ : Fintype O)
      (a : SphericalPicture.Data (O := O) (plusGraph Γ u) (plusLabel label u)
        WordPairing.inverseLetter)
      (l : PictureChains.Lift (plusGraph Γ u) (plusLabel label u) WordPairing.inverseLetter
        (Hyperbolic.eval (gen Γ label R)) a),
      Capped (Hyperbolic.eval (gen Γ label R)) a l := by
  classical
  let G := ConeGroup Γ label R
  let v : S₀ × Bool → G := Hyperbolic.eval (gen Γ label R)
  have hv : ∀ x, v (WordPairing.inverseLetter x) = (v x)⁻¹ := heval
  have hvalue : ∀ w : List (S₀ × Bool), WordCursor.value v w = Hyperbolic.value (gen Γ label R) w :=
    fun w => rfl
  let rel := InitialPicture.relWords Γ label (GraphPresentation.loopPath Γ R)
  have hrel : AlgebraicPictures.relations rel =
      GraphPresentation.relations Γ (GraphPresentation.roseLabel label) R :=
    GraphPresentation.loopPath_relations Γ label hl R
  have h1 : FreeGroup.mk (FreeGroup.invRev u) ∈ Subgroup.normalClosure (AlgebraicPictures.relations rel) := by
    rw [hrel]
    apply (PresentedGroup.mk_eq_one_iff).mp
    rw [← value_mk, Hyperbolic.value_invRev, hu1, inv_one]
  obtain ⟨ts, hts⟩ := AlgebraicPictures.expansion rel h1
  -- the free identity `u · (product of conjugated relators) = 1`
  let bs : List (G × List (S₀ × Bool)) := (1, u) :: WordFrames.framedWords (G := G) rel ts
  have hwords : (WordFrames.words bs).flatten = u ++ AlgebraicPictures.word rel ts := by
    simp only [bs, WordFrames.words, WordFrames.framedWords, List.map_cons, List.map_map,
      List.flatten_cons, AlgebraicPictures.word, List.flatMap_def]
    rfl
  have he : FreeGroup.mk (WordFrames.words bs).flatten = 1 := by
    rw [hwords, ← FreeGroup.mul_mk, hts, ← FreeGroup.inv_mk, mul_inv_cancel]
  have hrelator : ∀ i, WordCursor.value v (rel i) = 1 := by
    intro i
    rw [hvalue, value_mk]
    apply (PresentedGroup.mk_eq_one_iff).mpr
    apply Subgroup.subset_normalClosure
    rw [← hrel]
    exact ⟨i, rfl⟩
  have hcore : ∀ t : AlgebraicPictures.Term (A := S₀) (I := D),
      WordCursor.value v (t.core rel) = 1 := by
    intro t
    unfold AlgebraicPictures.Term.core
    split_ifs
    · exact hrelator _
    · rw [hvalue, Hyperbolic.value_invRev, ← hvalue, hrelator, inv_one]
  have hval : ∀ b ∈ bs, WordCursor.value v b.2 = 1 := by
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hu1
    · obtain ⟨t, _, rfl⟩ := List.mem_map.mp hb
      change WordCursor.value v (t.connector ++ t.core rel ++ FreeGroup.invRev t.connector) = 1
      rw [WordCursor.value_append, WordCursor.value_append, hcore, hvalue, hvalue,
        Hyperbolic.value_invRev]
      group
  have hg : ∀ b ∈ bs, b.1 = 1 := by
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · rfl
    · obtain ⟨t, _, rfl⟩ := List.mem_map.mp hb
      rfl
  obtain ⟨d0⟩ := WordFrames.of_identity v hv bs he hval hg
  let d1 := WordFrames.Data.strip v hv rel ts [(1, u)] d0
  -- the same blocks, read on darts of `Γ⁺`
  let tl : List (G × List (D ⊕ (Fin u.length × Bool))) :=
    ts.map (fun t => (WordCursor.value v t.connector,
      (InitialPicture.signedLoop Γ (GraphPresentation.loopPath Γ R) t).2.darts.map Sum.inl))
  let bsD : List (G × List (D ⊕ (Fin u.length × Bool))) := (1, outerDarts u) :: tl
  have hmap : WordFrames.mapLabels (plusLabel label u) bsD =
      [(1, u)] ++ WordFrames.framedCores v rel ts := by
    simp only [bsD, tl, WordFrames.mapLabels, WordFrames.framedCores, List.map_cons, List.map_map,
      List.singleton_append, outerDarts_labels]
    congr 1
    apply List.map_congr_left
    intro t _
    simp only [Function.comp_apply, List.map_map]
    congr 1
    have := InitialPicture.signedLoop_letters Γ label hl (GraphPresentation.loopPath Γ R) t
    simpa [GraphPresentation.Path.letters, Function.comp_def] using this
  let d2 : WordFrames.Data v WordPairing.inverseLetter (WordFrames.mapLabels (plusLabel label u) bsD) :=
    hmap ▸ d1
  have hc : WordBlocks.AllClosed (plusGraph Γ u) (WordFrames.words bsD) := by
    intro w hw
    simp only [bsD, tl, WordFrames.words, List.map_cons, List.map_map, List.mem_cons,
      List.mem_map, Function.comp_apply] at hw
    rcases hw with rfl | ⟨t, _, rfl⟩
    · exact outerDarts_closed u hn
    · let lp := InitialPicture.signedLoop Γ (GraphPresentation.loopPath Γ R) t
      exact ⟨Sum.inl lp.1, mapInl (u := u) lp.2, mapInl_darts _⟩
  -- the relator occurrences are `Γ`-darts
  have hinner : ∀ x : WordBlocks.Occ (WordFrames.words tl),
      ∃ e : D, WordBlocks.letter (WordFrames.words tl) x = Sum.inl e := by
    intro x
    rw [WordBlocks.letter_eq]
    have hm := List.get_mem (WordFrames.words tl).flatten (WordBlocks.coordinates _ x)
    obtain ⟨l, hl', hel⟩ := List.mem_flatten.mp hm
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hl'
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hb
    obtain ⟨e, _, he⟩ := List.mem_map.mp hel
    exact ⟨e, he.symm⟩
  have hlen : (outerDarts (D := D) u).length = u.length := List.length_ofFn
  have hget : ∀ j : Fin (outerDarts (D := D) u).length,
      (outerDarts (D := D) u).get j = Sum.inr (Fin.cast hlen j, true) := by
    intro j
    rw [List.get_eq_getElem]
    simp only [outerDarts, List.getElem_ofFn]
    try rfl
  let a := WordFrames.spherical (plusGraph Γ u) d2 hc
  let l := WordFrames.sphericalLift (plusGraph Γ u) d2 hc
  refine ⟨_, _, a, l, ?_, ?_, ?_⟩
  · -- no backward outer dart
    intro o i
    rcases o with j | x
    · change (outerDarts u).get j ≠ _
      rw [hget]
      simp
    · obtain ⟨e, he⟩ := hinner x
      change WordBlocks.letter (WordFrames.words tl) x ≠ _
      rw [he]
      exact Sum.inl_ne_inr
  · -- every outer letter occurs exactly once
    intro i
    refine ⟨Sum.inl (Fin.cast hlen.symm i), ?_, ?_⟩
    · change (outerDarts u).get (Fin.cast hlen.symm i) = _
      rw [hget]
      simp
    · intro o ho
      rcases o with j | x
      · change (outerDarts u).get j = _ at ho
        rw [hget] at ho
        simp only [Sum.inr.injEq, Prod.mk.injEq, and_true] at ho
        subst ho
        rfl
      · exfalso
        obtain ⟨e, he⟩ := hinner x
        change WordBlocks.letter (WordFrames.words tl) x = _ at ho
        rw [he] at ho
        exact Sum.inl_ne_inr ho
  · -- positions along the outer word
    intro o i ho
    rcases o with j | x
    · change (outerDarts u).get j = _ at ho
      rw [hget] at ho
      simp only [Sum.inr.injEq, Prod.mk.injEq, and_true] at ho
      have hj : j.val = i.val := congrArg Fin.val ho
      have hpos := WordFrames.sphericalLift_position (plusGraph Γ u) d2 hc (Sum.inl j)
      change (WordFrames.sphericalLift (plusGraph Γ u) d2 hc).position (Sum.inl j) = _
      rw [hpos]
      change 1 * WordCursor.cursor (v ∘ plusLabel label u) (outerDarts u) j.val = _
      rw [one_mul, WordCursor.cursor, prefixValue, hj, WordCursor.value, ← List.map_map,
        List.map_take (f := plusLabel label u), outerDarts_labels]
    · exfalso
      obtain ⟨e, he⟩ := hinner x
      change WordBlocks.letter (WordFrames.words tl) x = _ at ho
      rw [he] at ho
      exact Sum.inl_ne_inr ho

/-! ### Cone decompositions -/

variable {u : List (S₀ × Bool)} {k : ℕ}
  {b : SphericalPicture.Data (O := Fin k) (plusGraph Γ u) (plusLabel label u) WordPairing.inverseLetter}
  {lb : PictureChains.Lift (plusGraph Γ u) (plusLabel label u) WordPairing.inverseLetter
    (Hyperbolic.eval (gen Γ label R)) b}

/-- The `Γ`-dart of a cone occurrence. -/
def coneDart (o : {o : Fin k // (b.dart o).isLeft = true}) : D := (b.dart o.val).getLeft o.property

lemma coneDart_spec (o : {o : Fin k // (b.dart o).isLeft = true}) :
    b.dart o.val = Sum.inl (coneDart o) := by
  simp [coneDart]

variable (R) in
/-- **The cone decomposition** of a capped lifted picture. -/
noncomputable def coneDecomposition (hc : Capped (Hyperbolic.eval (gen Γ label R)) b lb) :
    Hyperbolic.ConeDecomposition (gen Γ label R) (routeBound R) u where
  O := {o : Fin k // (b.dart o).isLeft = true}
  σ := b.rotation.subtypePerm (fun o => by rw [PictureMap.isLeft_rotation])
  pos o := lb.position o.val
  cone o := lb.position o.val *
    (GraphPresentation.value Γ (GraphPresentation.roseLabel label) R (Γ.origin (coneDart o)))⁻¹
  step o := ⟨label (coneDart o), by
    change lb.position (b.rotation o.val) = _
    rw [lb.next, coneDart_spec]
    rfl⟩
  cone_next o := by
    let o' : {o : Fin k // (b.dart o).isLeft = true} :=
      ⟨b.rotation o.val, by rw [PictureMap.isLeft_rotation]; exact o.property⟩
    change lb.position (b.rotation o.val) *
      (GraphPresentation.value Γ (GraphPresentation.roseLabel label) R (Γ.origin (coneDart o')))⁻¹ = _
    have hcons := b.consistent o.val
    rw [coneDart_spec o, show b.dart (b.rotation o.val) = Sum.inl (coneDart o') from coneDart_spec o'] at hcons
    have horig : Γ.origin (Γ.reverse (coneDart o)) = Γ.origin (coneDart o') := by
      simpa [plusGraph, SumPort.graph] using hcons
    rw [← horig, GraphPresentation.edge, lb.next, coneDart_spec o, letter_eq]
    change lb.position o.val * Hyperbolic.eval (gen Γ label R) (label (coneDart o)) * _ = _
    group
  near o := ⟨(R.path (Γ.origin (coneDart o))).darts.map label, by
      rw [List.length_map]; exact route_le _, by
      rw [← value_route]
      group⟩
  integral F hF := by
    classical
    -- the charge of an occurrence
    let c : Fin k → ℤ := fun o =>
      F (lb.position o) (lb.position o * Hyperbolic.eval (gen Γ label R) (plusLabel label u (b.dart o)))
    have hpair : ∀ o, c (b.partner o) = -c o := by
      intro o
      simp only [c]
      rw [lb.pair, b.compatible, heval, mul_inv_cancel_right, hF]
    have hzero : ∑ o, c o = 0 := by
      have h1 : ∑ o, c (b.partner o) = ∑ o, c o := Equiv.sum_comp b.partner c
      simp only [hpair, Finset.sum_neg_distrib] at h1
      linarith
    -- split into cone and outer occurrences
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun o : Fin k => (b.dart o).isLeft = true) c
    rw [hzero] at hsplit
    have hcone : ∑ o ∈ Finset.univ.filter (fun o : Fin k => (b.dart o).isLeft = true), c o =
        ∑ o : {o : Fin k // (b.dart o).isLeft = true},
          F (lb.position o.val) (lb.position (b.rotation o.val)) := by
      have hs : ∑ o ∈ Finset.univ.filter (fun o : Fin k => (b.dart o).isLeft = true), c o =
          ∑ o : {o : Fin k // (b.dart o).isLeft = true}, c o.val :=
        Finset.sum_subtype _ (fun o => by simp) c
      rw [hs]
      apply Finset.sum_congr rfl
      intro o _
      simp only [c]
      rw [lb.next]
    have houter : ∑ o ∈ Finset.univ.filter (fun o : Fin k => ¬(b.dart o).isLeft = true), c o =
        Hyperbolic.wint (gen Γ label R) F 1 u := by
      have hs : ∑ o ∈ Finset.univ.filter (fun o : Fin k => ¬(b.dart o).isLeft = true), c o =
          ∑ o : {o : Fin k // ¬(b.dart o).isLeft = true}, c o.val :=
        Finset.sum_subtype _ (fun o => by simp) c
      rw [hs, ← hc.outerEquiv.symm.sum_comp, Hyperbolic.wint_eq_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [c, Capped.outerEquiv_symm_val, hc.occ_dart, one_mul]
      rw [hc.pos _ i (hc.occ_dart i), List.take_succ_eq_append_getElem i.isLt,
        Hyperbolic.value_append, Hyperbolic.value_singleton]
      rfl
    rw [hcone, houter] at hsplit
    have hσ : ∀ o : {o : Fin k // (b.dart o).isLeft = true},
        ((b.rotation.subtypePerm (fun o => by rw [PictureMap.isLeft_rotation])) o).val =
          b.rotation o.val := fun o => rfl
    simp only [hσ]
    linarith

end Cone

end Kaplansky.Exclusion

namespace Kaplansky.Exclusion

open OAI.TorsionFreeZeroDivisors
open PortSubdivision

section Hyp
variable {V D S₀ : Type} [Fintype V] [Fintype D] [DecidableEq S₀] [Finite S₀]
  {Γ : PortGraph V D} {label : D → S₀ × Bool} (R : GraphPresentation.Routes Γ)
  {isRoot : V → Prop} {ε d lam : ℝ} {L : ℕ}

/-- **Theorem B (iii)**: the cone group of a pattern-free graph is word-hyperbolic. The cone
decompositions have linear size `16/(13ε)·|w|` (paper Proposition 4.4) and cone radius the maximal
route length. -/
theorem wordHyperbolic_of_patternFree
    (pf : PatternFree Γ label WordPairing.inverseLetter isRoot ε d lam L) :
    Kaplansky.WordHyperbolic (ConeGroup Γ label R) := by
  have hl := pf.label_reverse
  have hε := pf.eps_pos
  have h13 : (0 : ℝ) < 13 * ε := mul_pos (by norm_num) hε
  refine Hyperbolic.wordHyperbolic_of_cones (gen Γ label R) ?_ (routeBound R) (16 / (13 * ε))
    (div_pos (by norm_num) h13).le ?_
  · intro g
    obtain ⟨x, rfl⟩ := PresentedGroup.mk_surjective _ g
    exact ⟨x.toWord, by rw [value_mk, FreeGroup.mk_toWord]⟩
  · intro w hne hcr hw1
    obtain ⟨O, _, a, l, hc⟩ := exists_capped hl R w hne hw1
    obtain ⟨k, b, lb, hcb, hr⟩ := exists_reduced_capped heval hl hc
    refine ⟨coneDecomposition R hcb, ?_⟩
    have hb := hcb.cone_bound pf hcr hr
    change ((Fintype.card {o : Fin k // (b.dart o).isLeft = true} : ℕ) : ℝ) ≤ _
    rw [Fintype.card_subtype, div_mul_eq_mul_div, le_div_iff₀ h13]
    nlinarith

end Hyp

end Kaplansky.Exclusion
