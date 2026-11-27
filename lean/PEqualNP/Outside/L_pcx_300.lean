import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_300

open Finset

variable {n : ℕ}

def t (τ : Equiv.Perm (Fin n)) (c : Fin n → Bool) (a : Fin n → Bool) (i : Fin n) : ℤ :=
  if a i ≠ xor (a (τ i)) (c i) then 1 else -1

def flip (k : Fin n) : Equiv.Perm (Fin n → Bool) :=
  Function.Involutive.toPerm (fun a => Function.update a k (!a k)) fun a => by
    ext j; by_cases h : j = k <;> simp [h]

lemma flip_apply (k : Fin n) (a : Fin n → Bool) : flip k a = Function.update a k (!a k) := rfl

lemma t_mul_t_le (τ : Equiv.Perm (Fin n)) (c a : Fin n → Bool) (i i' : Fin n) :
    t τ c a i * t τ c a i' ≤ 1 := by
  unfold t; split_ifs <;> norm_num

lemma sum_t_mul_t_eq_zero (τ : Equiv.Perm (Fin n)) (c : Fin n → Bool) {i i' : Fin n}
    (h1 : i ≠ i') (h2 : τ i ≠ i') (h3 : τ i' ≠ i') :
    ∑ a, t τ c a i * t τ c a i' = 0 := by
  have hi : ∀ a, t τ c (flip i' a) i = t τ c a i := fun a => by
    simp [t, flip_apply, Function.update_of_ne h1, Function.update_of_ne h2]
  have hi' : ∀ a, t τ c (flip i' a) i' = -t τ c a i' := fun a => by
    simp only [t, flip_apply, Function.update_self, Function.update_of_ne h3]
    cases a i' <;> cases xor (a (τ i')) (c i') <;> simp
  have := Equiv.sum_comp (flip i') fun a => t τ c a i * t τ c a i'
  simp only [hi, hi', mul_neg, sum_neg_distrib] at this
  linarith

lemma sum_sq_le (τ : Equiv.Perm (Fin n)) (c : Fin n → Bool) :
    ∑ a, (∑ i ∈ univ.filter (fun i => τ i ≠ i), t τ c a i) ^ 2 ≤ 2 * n * 2 ^ n := by
  set P := univ.filter (fun i => τ i ≠ i)
  have hN : ∑ _a : Fin n → Bool, (1 : ℤ) = 2 ^ n := by simp
  have key : ∀ i i', i' ∈ P → ∑ a, t τ c a i * t τ c a i' ≤
      (if i = i' then 2 ^ n else 0) + (if τ i = i' then 2 ^ n else 0) := by
    intro i i' hi'
    have hle : ∑ a, t τ c a i * t τ c a i' ≤ 2 ^ n :=
      hN ▸ sum_le_sum fun a _ => t_mul_t_le τ c a i i'
    have h0 : ∀ (p : Prop) [Decidable p], (0 : ℤ) ≤ if p then 2 ^ n else 0 := fun p _ => by
      split_ifs <;> positivity
    by_cases h1 : i = i'
    · have := h0 (τ i = i'); rw [ite_eq_left h1]; linarith
    by_cases h2 : τ i = i'
    · have := h0 (i = i'); rw [ite_eq_left h2]; linarith
    simp [h1, h2, sum_t_mul_t_eq_zero τ c h1 h2 (mem_filter.1 hi').2]
  calc ∑ a, (∑ i ∈ P, t τ c a i) ^ 2 = ∑ i ∈ P, ∑ i' ∈ P, ∑ a, t τ c a i * t τ c a i' := by
        simp_rw [sq, sum_mul_sum]; rw [sum_comm]; exact sum_congr rfl fun _ _ => sum_comm
    _ ≤ ∑ i ∈ P, ∑ i' ∈ P, ((if i = i' then 2 ^ n else 0) + (if τ i = i' then 2 ^ n else 0)) :=
        sum_le_sum fun i _ => sum_le_sum fun i' hi' => key i i' hi'
    _ ≤ ∑ i ∈ P, (2 * 2 ^ n : ℤ) := by
        refine sum_le_sum fun i _ => ?_
        rw [sum_add_distrib, sum_ite_eq, sum_ite_eq]
        split_ifs <;> linarith [pow_pos (two_pos : (0 : ℤ) < 2) n]
    _ ≤ 2 * n * 2 ^ n := by
        rw [sum_const, nsmul_eq_mul]
        have : (P.card : ℤ) ≤ n := by exact_mod_cast (card_filter_le _ _).trans (card_fin n).le
        nlinarith [pow_pos (two_pos : (0 : ℤ) < 2) n]

lemma sum_sign {α : Type*} (s : Finset α) (p : α → Prop) [DecidablePred p] :
    ∑ i ∈ s, (if p i then (1 : ℤ) else -1) = 2 * (s.filter p).card - s.card := by
  rw [sum_ite, sum_const, sum_const, ← card_filter_add_card_filter_not (s := s) p]
  simp only [nsmul_eq_mul]; push_cast; ring

lemma abs_sign_sub_t_le (p : Prop) [Decidable p] (τ : Equiv.Perm (Fin n)) (c a : Fin n → Bool)
    (i : Fin n) : |(if p then (1 : ℤ) else -1) - t τ c a i| ≤ 2 := by
  unfold t; split_ifs <;> norm_num

lemma central_iff {n : ℕ} (c : ℕ) (hn : 32 ≤ n) :
    16 * Nat.dist (2 * (17 * n / 32 + c)) n ≤ n ↔ c = 0 := by
  unfold Nat.dist; omega

end PEqualNP.Outside.L_pcx_300

open PEqualNP.Outside.L_pcx_300 Finset in
theorem PEqualNP.Outside.L_pcx_300 : ∀ (n r : ℕ) (M : Fin r → Equiv.Perm (Fin n)) (target : Fin r) (T : Finset (Fin n)),
  let V := Bool × Fin n
  let dist := fun (x : V → Bool) (j : Fin r) =>
    (Finset.univ.filter (fun i : Fin n => x (false,i) ≠ x (true,M j i))).card
  let central := fun D : ℕ => 16 * Nat.dist (2*D) n ≤ n
  8192*r < n → 128*T.card ≤ n →
  (∀ j : Fin r, j ≠ target →
    128*(Finset.univ.filter (fun i : Fin n => M j i = M target i)).card ≤ n) →
  ∃ base : V → Bool, ∀ x : V → Bool,
    (∀ i : Fin n, i ∉ T →
      x (false,i) = base (false,i) ∧ x (true,M target i) = base (true,M target i)) →
    dist x target = 17*n/32 + (T.filter (fun i => x (false,i) ≠ x (true,M target i))).card ∧
    (∀ j : Fin r, j ≠ target → central (dist x j)) ∧
    ((∀ j : Fin r, central (dist x j)) ↔ ∀ i ∈ T, x (false,i) = x (true,M target i)) := by
  intro n r M target T V dist central hr hT hM
  have hn : 8192 < n := by have := target.pos; omega
  set σ := M target

  set τ : Fin r → Equiv.Perm (Fin n) := fun j => σ⁻¹ * M j
  have hτ : ∀ j i, σ (τ j i) = M j i := fun j i => by simp [τ]

  obtain ⟨S, hST, hS⟩ := exists_subset_card_eq (s := Tᶜ) (n := 17 * n / 32)
    (by rw [card_compl, Fintype.card_fin]; omega)
  set m : Fin n → Bool := fun i => decide (i ∈ S)

  set X : (Fin n → Bool) → Fin r → ℤ := fun a j =>
    ∑ i ∈ univ.filter (fun i => τ j i ≠ i), t (τ j) (fun i => m (τ j i)) a i
  obtain ⟨a, ha⟩ : ∃ a, 4096 * ∑ j, X a j ^ 2 < (n : ℤ) ^ 2 := by
    by_contra! h
    have h1 := sum_le_sum fun a (_ : a ∈ univ) => h a
    have h2 : ∑ j, ∑ a, X a j ^ 2 ≤ ∑ _j : Fin r, (2 * n * 2 ^ n : ℤ) :=
      sum_le_sum fun j _ => sum_sq_le _ _
    rw [← mul_sum, sum_comm] at h1
    simp only [sum_const, card_univ, Fintype.card_fin, Fintype.card_fun, Fintype.card_bool,
      nsmul_eq_mul] at h1 h2
    have hr' : (8192 * r : ℤ) < n := by exact_mod_cast hr
    have hpos : (0 : ℤ) < n * 2 ^ n := by positivity
    push_cast at h1
    nlinarith
  refine ⟨fun v => if v.1 then xor (a (σ⁻¹ v.2)) (m (σ⁻¹ v.2)) else a v.2, fun x hx => ?_⟩
  have hxa : ∀ i ∉ T, x (false, i) = a i := fun i hi => (hx i hi).1
  have hxb : ∀ i ∉ T, x (true, σ i) = xor (a i) (m i) := fun i hi => by simpa using (hx i hi).2

  have hdt : dist x target =
      17 * n / 32 + (T.filter fun i => x (false, i) ≠ x (true, σ i)).card := by
    have hdisj : Disjoint S (T.filter fun i => x (false, i) ≠ x (true, σ i)) :=
      disjoint_left.2 fun i hiS hiT => mem_compl.1 (hST hiS) (mem_filter.1 hiT).1
    show #(univ.filter fun i => x (false, i) ≠ x (true, σ i)) = _
    rw [← hS, ← card_union_of_disjoint hdisj]
    congr 1
    ext i
    by_cases hi : i ∈ T
    · have : i ∉ S := fun h => mem_compl.1 (hST h) hi
      simp [hi, this]
    · cases h : a i <;> simp [hi, hxa i hi, hxb i hi, m, h]

  have hother : ∀ j, j ≠ target → central (dist x j) := by
    intro j hj
    set c : Fin n → Bool := fun i => m (τ j i)
    set Sx := ∑ i, (if x (false, i) ≠ x (true, M j i) then (1 : ℤ) else -1) with hSx
    set Sb := ∑ i, t (τ j) c a i
    set F := ∑ i ∈ univ.filter (fun i => ¬τ j i ≠ i), t (τ j) c a i
    have e : (2 * dist x j : ℤ) - n = Sx := by rw [hSx, sum_sign, card_univ, Fintype.card_fin]

    have hdiff : |Sx - Sb| ≤ 4 * T.card := by
      rw [← sum_sub_distrib]
      refine (abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ i, |(if x (false, i) ≠ x (true, M j i) then (1 : ℤ) else -1) - t (τ j) c a i|
          ≤ ∑ i, (2 * (if i ∈ T then 1 else 0) + 2 * (if τ j i ∈ T then 1 else 0) : ℤ) := by
            refine sum_le_sum fun i _ => ?_
            have h0 := abs_sign_sub_t_le (x (false, i) ≠ x (true, M j i)) (τ j) c a i
            have hA : (0 : ℤ) ≤ if i ∈ T then 1 else 0 := by split_ifs <;> norm_num
            have hB : (0 : ℤ) ≤ if τ j i ∈ T then 1 else 0 := by split_ifs <;> norm_num
            by_cases h1 : i ∈ T
            · have : (if i ∈ T then (1 : ℤ) else 0) = 1 := ite_eq_left h1
              linarith
            by_cases h2 : τ j i ∈ T
            · have : (if τ j i ∈ T then (1 : ℤ) else 0) = 1 := ite_eq_left h2
              linarith
            rw [← hτ j i, hxa i h1, hxb _ h2]
            simp [t, c, h1, h2]
        _ = 4 * T.card := by
            rw [sum_add_distrib, ← mul_sum, ← mul_sum,
              Equiv.sum_comp (τ j) fun i => if i ∈ T then (1 : ℤ) else 0]
            simp; ring

    have hsplit : X a j + F = Sb := sum_filter_add_sum_filter_not _ _ _
    have hfix : |F| ≤ (univ.filter fun i => M j i = σ i).card := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      rw [show univ.filter (fun i => ¬τ j i ≠ i) = univ.filter fun i => M j i = σ i from
        filter_congr fun i _ => by simp [τ, Equiv.symm_apply_eq]]
      calc _ ≤ ∑ _i ∈ univ.filter (fun i => M j i = σ i), (1 : ℤ) :=
            sum_le_sum fun i _ => by unfold t; split_ifs <;> norm_num
        _ = _ := by simp
    have hfix' : (128 * (univ.filter fun i => M j i = σ i).card : ℤ) ≤ n := by
      exact_mod_cast hM j hj
    have hX : |64 * X a j| < n := by
      refine abs_lt_of_sq_lt_sq ?_ (by positivity)
      have := single_le_sum (fun j _ => sq_nonneg (X a j)) (mem_univ j)
      nlinarith
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℤ) < 64)] at hX
    have hT' : (128 * T.card : ℤ) ≤ n := by exact_mod_cast hT
    have h3 := abs_sub_abs_le_abs_sub Sx Sb
    have h4 : |Sb| ≤ |X a j| + |F| := hsplit ▸ abs_add_le _ _
    have hb : 128 * |Sx| < 7 * n := by linarith
    have h1 := le_abs_self Sx
    have h2 := neg_abs_le Sx
    show 16 * Nat.dist (2 * dist x j) n ≤ n
    unfold Nat.dist
    omega
  refine ⟨hdt, hother, ⟨fun h => ?_, fun h j => ?_⟩⟩
  · have h0 := (central_iff _ (by omega)).1 (hdt ▸ h target)
    intro i hi
    simpa using filter_eq_empty_iff.1 (card_eq_zero.1 h0) hi
  · by_cases hj : j = target
    · subst hj
      show 16 * Nat.dist (2 * dist x j) n ≤ n
      rw [hdt, central_iff _ (by omega), card_eq_zero, filter_eq_empty_iff]
      simpa using h
    · exact hother j hj
