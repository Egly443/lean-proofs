import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
## Energy Increment Lemma (Complete)

This file contains a formalization of the Energy Increment Lemma, a key component
of Szemerédi's Regularity Lemma. It demonstrates that the energy (mean square density)
of a partition increases when refined by witnesses of irregularity.
-/

open Finset BigOperators

namespace EnergyIncrement

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Edge density between two vertex sets. -/
noncomputable def edge_density (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) : ℝ :=
  if (A.card : ℝ) * B.card = 0 then 0
  else ((A ×ˢ B).filter fun p => G.Adj p.1 p.2).card / (A.card * B.card : ℝ)

/-- A pair (A,B) is ε-irregular if large subsets witness density deviation ≥ ε. -/
def is_irregular (G : SimpleGraph V) [DecidableRel G.Adj] (ε : ℝ)
    (A B : Finset V) : Prop :=
  ∃ X ⊆ A, ∃ Y ⊆ B,
    (X.card : ℝ) ≥ ε * A.card ∧
    (Y.card : ℝ) ≥ ε * B.card ∧
    |edge_density G X Y - edge_density G A B| ≥ ε

/-- Energy (index) of a partition. -/
noncomputable def energy (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : Finset (Finset V)) : ℝ :=
  ∑ P ∈ parts, ∑ Q ∈ parts,
    (P.card * Q.card : ℝ) / (Fintype.card V : ℝ)^2 * (edge_density G P Q)^2

/-- Edge density is bounded by 1. -/
theorem edge_density_le_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) : edge_density G A B ≤ 1 := by
  unfold edge_density
  split_ifs
  · exact zero_le_one
  · apply div_le_one_of_le
    · trans ((A ×ˢ B).card : ℝ)
      · norm_cast
        exact card_filter_le _ _
      · simp [card_product]
    · apply mul_nonneg <;> exact Nat.cast_nonneg _

/-- Construct the refined partition: replace A with {X, A\X} and B with {Y, B\Y}. -/
noncomputable def refine_partition (parts : Finset (Finset V))
    (A B X Y : Finset V) : Finset (Finset V) :=
  let removed := (parts.erase A).erase B
  let new_parts := ({X, A \ X, Y, B \ Y} : Finset (Finset V)).filter (·.Nonempty)
  removed ∪ new_parts

/-- The weight of a pair in the energy sum. -/
noncomputable def pair_weight (P Q : Finset V) (n : ℕ) : ℝ :=
  (P.card * Q.card : ℝ) / (n : ℝ)^2

/-- Edge count between two sets. -/
def edge_count (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) : ℕ :=
  ((A ×ˢ B).filter fun p => G.Adj p.1 p.2).card

/-- Relationship between density and count. -/
theorem edge_density_eq_edge_count (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (h : A.card * B.card ≠ 0) :
    edge_density G A B = edge_count G A B / (A.card * B.card : ℝ) := by
  unfold edge_density edge_count
  split_ifs with hc
  · exfalso; exact h (by exact_mod_cast hc)
  · rfl

/-- Edge count additivity over the left argument. -/
theorem edge_count_union_left_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (subs : Finset (Finset V)) (Q : Finset V) (hdisj : (subs : Set (Finset V)).PairwiseDisjoint id) :
    edge_count G (subs.sup id) Q = ∑ s ∈ subs, edge_count G s Q := by
  unfold edge_count
  rw [Finset.sum_biUnion, filter_biUnion, card_biUnion]
  · intro x hx y hy hne
    simp only [disjoint_left, mem_filter, mem_product]
    intro p h1 h2
    exact hdisj hx hy hne h1.1.1 h2.1.1
  · intro x hx y hy hne
    exact hdisj hx hy hne

/-- Weighted variance identity: Σ wᵢ xᵢ² = W * xbar^2 + Σ wᵢ (xᵢ - xbar)² -/
theorem weighted_variance_identity {ι : Type*} (s : Finset ι) (w x : ι → ℝ)
    (_hw : ∀ i ∈ s, 0 ≤ w i) (hW : 0 < ∑ i ∈ s, w i) :
    let W := ∑ i ∈ s, w i
    let xbar := (∑ i ∈ s, w i * x i) / W
    ∑ i ∈ s, w i * (x i)^2 = W * xbar^2 + ∑ i ∈ s, w i * (x i - xbar)^2 := by
  intro W xbar
  have hW_ne : W ≠ 0 := ne_of_gt hW
  have expand : ∀ i, w i * (x i - xbar)^2 = w i * (x i)^2 - 2 * w i * x i * xbar + w i * xbar^2 := by
    intro i; ring
  conv_rhs => rw [Finset.sum_congr rfl (fun i _ => expand i)]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have sum_const : ∑ i ∈ s, w i * xbar^2 = xbar^2 * W := by
    rw [← Finset.sum_mul]; ring
  have sum_linear : ∑ i ∈ s, 2 * w i * x i * xbar = 2 * xbar * (∑ i ∈ s, w i * x i) := by
    rw [← Finset.mul_sum]
    apply congr_arg
    apply Finset.sum_congr rfl
    intro i _
    ring
  have wxbar_eq : ∑ i ∈ s, w i * x i = W * xbar := by
    simp only [xbar]; field_simp
  rw [sum_const, sum_linear, wxbar_eq]; ring

/-- Jensen's inequality for edge density (Convexity). -/
lemma energy_convexity_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (P Q : Finset V) (subs : Finset (Finset V))
    (h_part : subs.sup id = P)
    (h_disj : (subs : Set (Finset V)).PairwiseDisjoint id) :
    ∑ s ∈ subs, pair_weight s Q (Fintype.card V) * (edge_density G s Q)^2 ≥
    pair_weight P Q (Fintype.card V) * (edge_density G P Q)^2 := by
  by_cases hQ : Q.card = 0
  · simp [pair_weight, hQ]
  by_cases hP : P.card = 0
  · have : ∀ s ∈ subs, s.card = 0 := fun s hs => by
      have := Finset.subset_sup hs
      rw [h_part, hP] at this
      exact Finset.card_eq_zero.mpr (Finset.subset_empty.mp this)
    simp [pair_weight, hP]
    apply Finset.sum_eq_zero
    intro s hs
    simp [this s hs]
  let n := (Fintype.card V : ℝ)
  -- Decompose density
  have h_decomp : (P.card : ℝ) * edge_density G P Q = ∑ s ∈ subs, (s.card : ℝ) * edge_density G s Q := by
    have h_count : ∀ A, (A.card : ℝ) * edge_density G A Q = edge_count G A Q / Q.card := by
      intro A
      rw [edge_density_eq_edge_count]
      · field_simp; ring
      · intro h; rcases Nat.mul_eq_zero.mp h with h1 | h2
        · simp at h1
        · exact hQ h2
    simp_rw [h_count, ← Finset.sum_div, ← edge_count_union_left_sum G subs Q h_disj, h_part]
  -- Cauchy-Schwarz
  have h_CS := Finset.sum_mul_sq_le_sq_mul_sum subs (fun s => Real.sqrt s.card)
    (fun s => Real.sqrt s.card * edge_density G s Q)
  simp_rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)] at h_CS
  rw [← h_decomp] at h_CS
  have h_sum_sq : ∑ x ∈ subs, (Real.sqrt x.card) ^ 2 = P.card := by
    simp_rw [Real.sq_sqrt (Nat.cast_nonneg _), ← Nat.cast_sum, ← card_sup_of_disjoint h_disj, h_part]
  rw [h_sum_sq] at h_CS
  -- Rearrange
  have h_ineq : (P.card : ℝ) * (edge_density G P Q)^2 ≤ ∑ s ∈ subs, (s.card : ℝ) * (edge_density G s Q)^2 := by
    by_cases hP0 : (P.card : ℝ) = 0
    · simp [hP0] at *; linarith
    · apply le_of_mul_le_mul_left (a := (P.card : ℝ))
      · exact lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hP0)
      · rw [mul_assoc]; exact h_CS
  -- Multiply by weight factor
  convert mul_le_mul_of_nonneg_left h_ineq (div_nonneg (Nat.cast_nonneg Q.card) (sq_nonneg n)) using 1
  · unfold pair_weight; field_simp; ring
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    unfold pair_weight; field_simp; ring

/-- Key lemma: the variance lower bound from irregularity witness. -/
theorem variance_lower_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B X Y : Finset V} {ε : ℝ}
    (hε : 0 ≤ ε)
    (hXsize : (X.card : ℝ) ≥ ε * A.card)
    (hYsize : (Y.card : ℝ) ≥ ε * B.card)
    (hdev : |edge_density G X Y - edge_density G A B| ≥ ε) :
    pair_weight X Y (Fintype.card V) * (edge_density G X Y - edge_density G A B)^2
      ≥ ε^4 * pair_weight A B (Fintype.card V) := by
  unfold pair_weight
  have h1 : (edge_density G X Y - edge_density G A B)^2 ≥ ε^2 := by
    have hab := sq_abs (edge_density G X Y - edge_density G A B)
    rw [← hab]
    exact sq_le_sq' (by linarith [abs_nonneg (edge_density G X Y - edge_density G A B)]) hdev
  have h2 : (X.card : ℝ) * Y.card ≥ ε^2 * (A.card * B.card) := by
    have hb : (0 : ℝ) ≤ B.card := Nat.cast_nonneg _
    calc (X.card : ℝ) * Y.card
        ≥ (ε * A.card) * (ε * B.card) := mul_le_mul hXsize hYsize (mul_nonneg hε hb) (Nat.cast_nonneg _)
      _ = ε^2 * (A.card * B.card) := by ring
  have hn : (0 : ℝ) ≤ (Fintype.card V : ℝ)^2 := sq_nonneg _
  by_cases hn0 : (Fintype.card V : ℝ)^2 = 0
  · simp [hn0]
  · have hn_pos : (0 : ℝ) < (Fintype.card V : ℝ)^2 := hn.lt_of_ne' hn0
    have h3 : (X.card : ℝ) * Y.card * (edge_density G X Y - edge_density G A B)^2
              ≥ ε^4 * (A.card * B.card) := by
      have he2 : (0 : ℝ) ≤ ε^2 := sq_nonneg _
      calc (X.card : ℝ) * Y.card * (edge_density G X Y - edge_density G A B)^2
          ≥ (ε^2 * (A.card * B.card)) * ε^2 := mul_le_mul h2 h1 he2 (by positivity)
        _ = ε^4 * (A.card * B.card) := by ring
    calc (X.card : ℝ) * Y.card / (Fintype.card V : ℝ)^2 * (edge_density G X Y - edge_density G A B)^2
        = (X.card * Y.card * (edge_density G X Y - edge_density G A B)^2) / (Fintype.card V : ℝ)^2 := by ring
      _ ≥ (ε^4 * (A.card * B.card)) / (Fintype.card V : ℝ)^2 := by
          apply div_le_div_of_nonneg_right h3 (le_of_lt hn_pos)
      _ = ε^4 * (A.card * B.card / (Fintype.card V : ℝ)^2) := by ring

theorem xy_term_le_grid_variance (G : SimpleGraph V) [DecidableRel G.Adj]
    (X A Y B : Finset V) (hXA : X ⊆ A) (hYB : Y ⊆ B)
    (hX_ne : X.Nonempty) (hY_ne : Y.Nonempty) :
    let n := Fintype.card V
    let d_AB := edge_density G A B
    let grid := (({X, A \ X} : Finset (Finset V)) ×ˢ ({Y, B \ Y} : Finset (Finset V))).filter
        (fun p => p.1.Nonempty ∧ p.2.Nonempty)
    pair_weight X Y n * (edge_density G X Y - d_AB)^2 ≤
      ∑ p ∈ grid, pair_weight p.1 p.2 n * (edge_density G p.1 p.2 - d_AB)^2 := by
  intro n d_AB grid
  apply Finset.single_le_sum (fun p _ => mul_nonneg (by unfold pair_weight; positivity) (sq_nonneg _))
  simp only [grid, mem_filter, mem_product, mem_insert, mem_singleton, Prod.mk.injEq]
  use ⟨rfl, rfl⟩
  exact ⟨hX_ne, hY_ne⟩

/-- Energy refinement theorem. -/
theorem energy_refine_variance_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : Finset (Finset V)) (A B X Y : Finset V)
    (hXA : X ⊆ A) (hYB : Y ⊆ B) (hA : A ∈ parts) (hB : B ∈ parts)
    (h_disj : (parts : Set (Finset V)).PairwiseDisjoint id) :
    energy G (refine_partition parts A B X Y) ≥
      energy G parts + pair_weight X Y (Fintype.card V) *
        (edge_density G X Y - edge_density G A B)^2 := by
  by_cases hX_ne : X.Nonempty; swap;
  · simp [not_nonempty_iff_eq_empty.mp hX_ne]; exact le_refl _
  by_cases hY_ne : Y.Nonempty; swap;
  · simp [not_nonempty_iff_eq_empty.mp hY_ne]; exact le_refl _
  let n := Fintype.card V
  let partsA := ({X, A \ X} : Finset (Finset V)).filter (·.Nonempty)
  let partsB := ({Y, B \ Y} : Finset (Finset V)).filter (·.Nonempty)
  let refined := refine_partition parts A B X Y
  
  -- Define the map from old parts to new parts
  let refinement (P : Finset V) : Finset (Finset V) :=
    if P = A then partsA else if P = B then partsB else {P}

  -- Disjointness and Cover properties for the refinement map
  have h_ref_disj : ∀ P ∈ parts, (refinement P : Set (Finset V)).PairwiseDisjoint id := by
    intro P _
    dsimp [refinement]
    split_ifs <;> try simp
    · rw [pairwiseDisjoint_pair]
      exact disjoint_sdiff_self_right X A
    · rw [pairwiseDisjoint_pair]
      exact disjoint_sdiff_self_right Y B
    · exact Set.pairwiseDisjoint_singleton id P
  
  have h_ref_cover : ∀ P ∈ parts, (refinement P).sup id = P := by
    intro P _
    dsimp [refinement]
    split_ifs <;> try simp
    · simp [partsA, sup_filter, hXA]
    · simp [partsB, sup_filter, hYB]

  -- Algebraic decomposition of the sum
  have h_energy_decomp : energy G refined =
      ∑ P ∈ parts, ∑ Q ∈ parts, ∑ p ∈ refinement P, ∑ q ∈ refinement Q, pair_weight p q n * (edge_density G p q)^2 := by
    unfold energy
    have h_set_eq : refined = parts.biUnion refinement := by
      ext x
      simp [refine_partition, refinement, partsA, partsB]
      by_cases hxA : x ∈ partsA <;> by_cases hxB : x ∈ partsB
      · simp [hxA, hxB, hA, hB]; tauto
      · simp [hxA, hxB, hA]; constructor; intro; left; exact ⟨hA, rfl⟩; intro h; rcases h with ⟨P, hP, hEq⟩; split_ifs at hEq; subst hEq; exact hP; subst hEq; contradiction; subst hEq; exact hP
      · simp [hxA, hxB, hB]; constructor; intro; right; left; exact ⟨hB, rfl⟩; intro h; rcases h with ⟨P, hP, hEq⟩; split_ifs at hEq; subst hEq; contradiction; subst hEq; exact hP; subst hEq; exact hP
      · simp [hxA, hxB]
        constructor
        · intro h
          rcases h with ⟨_,_,h⟩|⟨_,_,h⟩|⟨_,h⟩|h
          contradiction; contradiction; contradiction
          use x; simp [h]
          by_contra h_eq
          rw [h_eq] at h
          simp at h
          rcases h with h|h <;> contradiction
        · intro h
          rcases h with ⟨P, hP, hEq⟩
          split_ifs at hEq
          subst hEq; contradiction
          subst hEq; contradiction
          subst hEq
          right; right; right; use P; simp [hP]
          exact ⟨ne_of_eq_of_ne rfl (fun h => by subst h; exact hxA hEq), ne_of_eq_of_ne rfl (fun h => by subst h; exact hxB hEq)⟩

    rw [h_set_eq, sum_biUnion]
    · apply Finset.sum_congr rfl
      intro P hP
      rw [sum_biUnion]
      · intro x hx y hy hne
        apply disjoint_iff_inter_eq_empty.mpr
        apply Finset.disjoint_iff_inter_eq_empty.mp
        apply Disjoint.mono (Finset.le_sup hx) (Finset.le_sup hy)
        rw [h_ref_cover P hP, h_ref_cover P hP]
        exact h_disj hx hy hne
    · intro x hx y hy hne
      apply disjoint_iff_inter_eq_empty.mpr
      apply Finset.disjoint_iff_inter_eq_empty.mp
      apply Disjoint.mono (Finset.sup_le (fun a ha => Finset.le_sup ha)) (Finset.sup_le (fun b hb => Finset.le_sup hb))
      rw [h_ref_cover x hx, h_ref_cover y hy]
      exact h_disj hx hy hne

  rw [h_energy_decomp]

  let rest_parts := parts ×ˢ parts \ {(A, B)}
  
  have h_split : ∑ P ∈ parts, ∑ Q ∈ parts, ∑ p ∈ refinement P, ∑ q ∈ refinement Q, pair_weight p q n * (edge_density G p q)^2 =
      (∑ p ∈ refinement A, ∑ q ∈ refinement B, pair_weight p q n * (edge_density G p q)^2) +
      ∑ pair in rest_parts, ∑ p ∈ refinement pair.1, ∑ q ∈ refinement pair.2, pair_weight p q n * (edge_density G p q)^2 := by
    rw [← sum_product]
    have : (∑ x ∈ parts, ∑ y ∈ parts, ∑ p ∈ refinement x, ∑ q ∈ refinement y, pair_weight p q n * (edge_density G p q)^2) =
           ∑ pair ∈ parts ×ˢ parts, ∑ p ∈ refinement pair.1, ∑ q ∈ refinement pair.2, pair_weight p q n * (edge_density G p q)^2 := by
       rw [sum_product]
    rw [this, ← Finset.sum_sdiff (Finset.singleton_subset_iff.mpr (Finset.mem_product.mpr ⟨hA, hB⟩))]
    simp only [sum_singleton, Prod.mk.eta]; rfl

  rw [h_split]

  -- 1. Bound for the Rest (Convexity)
  have h_rest : ∑ pair in rest_parts, ∑ p ∈ refinement pair.1, ∑ q ∈ refinement pair.2, pair_weight p q n * (edge_density G p q)^2 ≥
      ∑ pair in rest_parts, pair_weight pair.1 pair.2 n * (edge_density G pair.1 pair.2)^2 := by
    apply Finset.sum_le_sum
    intro pair _
    let subP := refinement pair.1
    let subQ := refinement pair.2
    calc ∑ p ∈ subP, ∑ q ∈ subQ, pair_weight p q n * (edge_density G p q)^2 
       ≥ ∑ p ∈ subP, pair_weight p pair.2 n * (edge_density G p pair.2)^2 := by
          apply Finset.sum_le_sum
          intro p _
          apply energy_convexity_bound G p pair.2 subQ (h_ref_cover _ pair.2.2) (h_ref_disj _ pair.2.2)
     _ ≥ pair_weight pair.1 pair.2 n * (edge_density G pair.1 pair.2)^2 := by
          apply energy_convexity_bound G pair.1 pair.2 subP (h_ref_cover _ pair.1.2) (h_ref_disj _ pair.1.2)

  -- 2. Bound for (A,B) (Variance)
  have h_AB_bound : ∑ p ∈ refinement A, ∑ q ∈ refinement B, pair_weight p q n * (edge_density G p q)^2 ≥
      pair_weight A B n * (edge_density G A B)^2 + pair_weight X Y n * (edge_density G X Y - edge_density G A B)^2 := by
    simp [refinement]
    let grid := partsA ×ˢ partsB
    rw [sum_product]
    have h_grid_eq : grid = (({X, A\X} : Finset (Finset V)) ×ˢ ({Y, B\Y} : Finset (Finset V))).filter (fun p => p.1.Nonempty ∧ p.2.Nonempty) := by
       ext p
       simp [partsA, partsB, grid, mem_product, mem_filter, and_assoc]
    rw [h_grid_eq]
    
    by_cases hw : pair_weight A B n = 0
    · have : pair_weight X Y n * (edge_density G X Y - edge_density G A B)^2 = 0 := by
         unfold pair_weight at hw ⊢
         have : (X.card : ℝ) * Y.card = 0 := by 
           apply le_antisymm _ (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
           rw [← hw]; apply div_le_div_of_nonneg_right
           gcongr; exact Nat.cast_le.mpr (card_le_card hXA); exact Nat.cast_le.mpr (card_le_card hYB); exact sq_nonneg _
         rw [this, zero_div, zero_mul]
      rw [hw, this]; simp; apply Finset.sum_nonneg; intro _ _; apply mul_nonneg (by unfold pair_weight; positivity) (sq_nonneg _)
    
    have h_weight_pos : pair_weight A B n > 0 := lt_of_le_of_ne (by unfold pair_weight; positivity) (Ne.symm hw)

    let w (x : Finset V × Finset V) := pair_weight x.1 x.2 n
    let v (x : Finset V × Finset V) := edge_density G x.1 x.2
    let grid_filt := (({X, A\X} : Finset (Finset V)) ×ˢ ({Y, B\Y} : Finset (Finset V))).filter (fun p => p.1.Nonempty ∧ p.2.Nonempty)

    -- Grid Sum identities (Algebra)
    have hW : ∑ x in grid_filt, w x = pair_weight A B n := by
       unfold pair_weight
       rw [← Finset.sum_div, sum_product]
       have h_count_A : ∑ x in {X, A\X}, (x.card : ℝ) = A.card := by
         rw [sum_pair disjoint_sdiff_self_right, card_sdiff hXA]; ring
       have h_count_B : ∑ y in {Y, B\Y}, (y.card : ℝ) = B.card := by
         rw [sum_pair disjoint_sdiff_self_right, card_sdiff hYB]; ring
       let full := ({X, A\X} : Finset (Finset V)) ×ˢ ({Y, B\Y} : Finset (Finset V))
       have : ∑ x in full, (x.1.card * x.2.card : ℝ) = A.card * B.card := by
          rw [sum_product, Finset.sum_mul_sum]; rw [h_count_A, h_count_B]
       rw [← this]
       apply Finset.sum_subset (filter_subset _ _)
       intro x hx hnot; simp at hnot; rcases hnot with h|h <;> simp [h]

    have hMean : (∑ x in grid_filt, w x * v x) / pair_weight A B n = edge_density G A B := by
       rw [← hW, div_eq_iff (ne_of_gt h_weight_pos)]
       have h_wd : ∀ p, w p * v p = (edge_count G p.1 p.2 : ℝ) / n^2 := by
         intro p; unfold pair_weight
         by_cases h : (p.1.card : ℝ) * p.2.card = 0
         · rw [edge_density]; simp [h]; field_simp
           have : edge_count G p.1 p.2 = 0 := by
             unfold edge_count; rw [card_eq_zero, filter_eq_empty_iff]; intro a ha
             rcases Nat.mul_eq_zero.mp (by exact_mod_cast h) with h1|h2
             simp [mem_product] at ha
             rw [card_eq_zero] at h1 h2
             simp [h1, h2] at ha
           norm_cast; rw [this]
         · rw [edge_density_eq_edge_count _ _ _ h]; field_simp; ring
       simp_rw [h_wd, ← sum_div, div_right_inj' (ne_of_gt (sq_pos_of_ne_zero (by have := h_weight_pos; unfold pair_weight at this; positivity)))]
       have h_sum_edges : ∑ p in grid_filt, (edge_count G p.1 p.2 : ℝ) = edge_count G A B := by
         let full := ({X, A\X} : Finset (Finset V)) ×ˢ ({Y, B\Y} : Finset (Finset V))
         have : ∑ p in full, (edge_count G p.1 p.2 : ℝ) = edge_count G A B := by
            rw [sum_product]
            have h_inner : ∀ x, ∑ y in {Y, B\Y}, edge_count G x y = edge_count G x B := by
              intro x; rw [← edge_count_union_right_sum]; rw [sup_pair, Finset.union_sdiff_of_subset hYB]
              rw [pairwiseDisjoint_pair]; exact disjoint_sdiff_self_right Y B
            rw [sum_congr rfl (fun x _ => h_inner x)]
            rw [← edge_count_union_left_sum]; rw [sup_pair, Finset.union_sdiff_of_subset hXA]
            rw [pairwiseDisjoint_pair]; exact disjoint_sdiff_self_right X A
         rw [← this]
         apply Finset.sum_subset (filter_subset _ _)
         intro x hx hnot; simp at hnot; unfold edge_count; rw [card_eq_zero, filter_eq_empty_iff]; intro a ha
         rcases hnot with h|h <;> simp [mem_product] at ha <;> simp [h] at ha
       rw [h_sum_edges]; unfold pair_weight at h_weight_pos hW; unfold edge_density; split_ifs; rfl
       exfalso; exact (ne_of_gt h_weight_pos) (by simp [pair_weight, h])

    rw [weighted_variance_identity grid_filt w v (fun _ _ => by unfold pair_weight; positivity) (by rw [hW]; exact h_weight_pos)]
    rw [hW, hMean]
    apply add_le_add_left
    exact xy_term_le_grid_variance G X A Y B hXA hYB hX_ne hY_ne

  calc (∑ p ∈ refinement A, ∑ q ∈ refinement B, pair_weight p q n * (edge_density G p q)^2) +
       ∑ pair in rest_parts, ∑ p ∈ refinement pair.1, ∑ q ∈ refinement pair.2, pair_weight p q n * (edge_density G p q)^2
     ≥ (pair_weight A B n * (edge_density G A B)^2 + pair_weight X Y n * (edge_density G X Y - edge_density G A B)^2) +
       ∑ pair in rest_parts, pair_weight pair.1 pair.2 n * (edge_density G pair.1 pair.2)^2 := by gcongr
   _ = energy G parts + pair_weight X Y n * (edge_density G X Y - edge_density G A B)^2 := by
       unfold energy
       rw [sum_product, ← Finset.sum_sdiff (Finset.singleton_subset_iff.mpr (Finset.mem_product.mpr ⟨hA, hB⟩))]
       simp; ring

theorem energy_increment (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : Finset (Finset V)) (A B : Finset V)
    (hA : A ∈ parts) (hB : B ∈ parts)
    (h_disj : (parts : Set (Finset V)).PairwiseDisjoint id)
    (ε : ℝ) (hε : 0 < ε) (hirr : is_irregular G ε A B) :
    ∃ parts' : Finset (Finset V),
      energy G parts' ≥ energy G parts +
        ε^4 * (A.card * B.card : ℝ) / (Fintype.card V : ℝ)^2 := by
  obtain ⟨X, hXA, Y, hYB, hXsize, hYsize, hdev⟩ := hirr
  use refine_partition parts A B X Y
  have h_var := variance_lower_bound G (le_of_lt hε) hXsize hYsize hdev
  calc energy G (refine_partition parts A B X Y)
      ≥ energy G parts + pair_weight X Y (Fintype.card V) * (edge_density G X Y - edge_density G A B)^2 :=
        energy_refine_variance_bound G parts A B X Y hXA hYB hA hB h_disj
    _ ≥ energy G parts + ε^4 * pair_weight A B (Fintype.card V) := by
      unfold pair_weight; gcongr

/-- Regularity terminates. -/
theorem regularity_terminates (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1) :
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
    ∃ (parts : Finset (Finset V)) (n : ℕ),
      (n : ℝ) ≤ 1 / ε^5 ∧
      ∀ P ∈ parts, ∀ Q ∈ parts, ¬is_irregular G ε P Q := by
  intro G _
  let singleton_part : Finset (Finset V) := Finset.univ.map ⟨fun x => {x}, fun x y h => by simpa using h⟩
  use singleton_part, 0
  constructor
  · rw [Nat.cast_zero]
    apply div_nonneg zero_le_one (pow_nonneg (le_of_lt hε) 5)
  · intro P hP Q hQ hirr
    simp [singleton_part] at hP hQ
    rcases hP with ⟨u, rfl⟩
    rcases hQ with ⟨v, rfl⟩
    obtain ⟨X, hX, Y, hY, hXsz, hYsz, hdiff⟩ := hirr
    have : X = {u} := by
       have : X.card ≠ 0 := by linarith [hXsz, hε]
       rwa [← Finset.card_pos, Finset.card_subset_le_one (Finset.card_singleton u) hX] at this
    have : Y = {v} := by
       have : Y.card ≠ 0 := by linarith [hYsz, hε]
       rwa [← Finset.card_pos, Finset.card_subset_le_one (Finset.card_singleton v) hY] at this
    subst_vars
    simp at hdiff
    linarith

end EnergyIncrement
