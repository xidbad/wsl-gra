import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

set_option autoImplicit true
set_option linter.style.multiGoal false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.flexible false

notation "E"  => !![1, 0; 0, 1]    -- 位数 1, det =  1, tr =  2, t - 1
notation "-E" => !![-1, 0; 0, -1]  -- 位数 2, det =  1, tr = -2, t + 1
notation "P1" => !![1, 0; 0, -1]   -- 位数 2, det = -1, tr =  0, (t + 1)(t - 1)
notation "P2" => !![0, -1; 1, -1]  -- 位数 3, det =  1, tr = -1, t^2 + t + 1
notation "P3" => !![0, 1; -1, 0]   -- 位数 4, det =  1, tr =  0, t^2 + 1
notation "P4" => !![0, -1; 1, 1]   -- 位数 6, det =  1, tr =  1, t^2 - t + 1

open Matrix Polynomial minpoly Finset Irreducible
namespace Nat

variable (M : GL (Fin 2) ℚ)

local notation "Φ" n => cyclotomic n ℚ


-- 最小多項式の次数は2以下
lemma minpoly_deg_le_two : (minpoly ℚ M.val).natDegree ≤ 2 :=
  calc
    _ ≤ (charpoly M.val).natDegree := by
      apply natDegree_le_of_dvd (dvd ℚ M.val (aeval_self_charpoly M.val))
      · apply ne_zero_of_natDegree_gt
        show 0 < (charpoly M.val).natDegree
        simp [charpoly_natDegree_eq_dim]
    _ = 2 := charpoly_natDegree_eq_dim M.val


-- 最小多項式は X^n - 1 を割り切る
lemma minpoly_dvd_X_pow_sub_one (h' : n = orderOf M.val) :
    minpoly ℚ M.val ∣ X ^ n - 1 := by
  apply dvd; simp [h', pow_orderOf_eq_one]


-- 最小多項式にはモニックな既約因子が存在する
lemma exist_normalizefactor : ∃ f : ℚ[X], Monic f ∧ Irreducible f ∧ f ∣ minpoly ℚ M.val := by
  apply exists_monic_irreducible_factor
  rw [isUnit_iff_degree_eq_zero]; push_neg
  exact Ne.symm (_root_.ne_of_lt (degree_pos (isIntegral M.val)))


-- 最小多項式の任意のモニックな既約因子はnの約数iについて第i円分多項式と一致する
lemma normalizedfactor_eq_cyclotomic (h : IsOfFinOrder M.val) (h' : n = orderOf M.val)
    (f : ℚ[X]) (fmon : Monic f) (firr : Irreducible f) (fdvd : f ∣ minpoly ℚ M.val) :
    ∃ i ∈ n.divisors, f = Φ i := by
  have h₁ : ∃ i ∈ n.divisors, f ∣ Φ i := by
    rw [← (prime firr).dvd_finset_prod_iff, prod_cyclotomic_eq_X_pow_sub_one (by simp [h', h])]
    exact dvd_trans fdvd (minpoly_dvd_X_pow_sub_one M h')
  obtain ⟨i, imem, hdvd'⟩ := h₁
  use i, imem
  rcases associated_of_dvd firr (cyclotomic.irreducible_rat (pos_of_mem_divisors imem)) hdvd' with ⟨u, feq⟩
  rw [← feq, left_eq_mul₀ (Monic.ne_zero fmon), ← Monic.isUnit_iff]
  · exact u.isUnit
  · apply Monic.of_mul_monic_left fmon
    rw [feq]; exact cyclotomic.monic i ℚ


-- 円分多項式の次数はオイラーのトーシェント関数と一致する
lemma cyclotomic_deg_eq_totient (n : ℕ) : (Φ n).natDegree = φ n := natDegree_cyclotomic n ℚ


-- φ n = 2 ならば n は2と3以外の素因数をもたない
lemma n_exist (n : ℕ) (h : n ≠ 0) (h' : φ n = 2) : n = 2 ^ (n.factorization 2) * 3 ^ (n.factorization 3) := by
  have h₁ : n.primeFactors ⊆ ({2, 3} : Finset ℕ) := by
    intro p pmem; rw [mem_insert, mem_singleton]
    rw [totient_eq_prod_factorization h] at h'
    have h1 : p ^ (n.factorization p - 1) * (p - 1) ∣ 2 := by
      rw [← h']; apply dvd_prod_of_mem; exact pmem
    have h2 : p - 1 ∣ 2 := dvd_of_mul_left_dvd h1
    have h3 : p - 1 ≤ 2 := le_of_dvd (by decide) h2
    interval_cases hu : p - 1 <;> omega
  nth_rw 1 [← factorization_prod_pow_eq_self h, prod_factorization_eq_prod_primeFactors]
  rw [prod_subset h₁]
  · rw [prod_pair]; decide
  · intro p pmem pnot; rw [pow_eq_one_iff]; right
    exact notMem_support_iff.mp pnot


-- φ n = 2 ならば n = 3, 4, 6
lemma totient_eq_two_iff (n : ℕ) (h : n ≠ 0) : φ n = 2 ↔ n ∈ ({3, 4, 6} : Finset ℕ) := by
  constructor <;> intro h'
  · have n_exist := n_exist n h h'
    rw [n_exist, totient_mul] at h'
    set a := n.factorization 2
    set b := n.factorization 3
    · have h₁ : φ (2 ^ a) ≤ 2 := by
        apply le_of_dvd (by decide)
        nth_rw 2 [← h']; apply dvd_mul_right
      interval_cases h₂ : φ (2 ^ a)
      -- φ (2^a) = 0
      · linarith
      -- φ (2^a) = 1
      · rw [totient_eq_one_iff] at h₂
        rw [one_mul] at h'
        have hb : b = 1 := by
          have bneq : b ≠ 0 := by
            by_contra
            rw [this, pow_zero, totient_one] at h'; linarith
          rw [totient_prime_pow] at h'
          · simp at h'; omega
          · decide
          · exact pos_of_ne_zero bneq
        rcases h₂ with one | two
        -- 2^a = 1
        · rw [n_exist, one, one_mul, hb, pow_one]; decide
        -- 2^a = 2
        · rw [n_exist, two, hb, pow_one]; decide
      -- φ (2^a) = 2
      · rw [mul_eq_left (by decide), totient_eq_one_iff] at h'
        rcases h' with one | two
        -- 3^b = 1
        · rw [one, mul_one] at n_exist
          have ha : a = 2 := by
            rw [totient_prime_pow] at h₂
            · simp [pow_eq_self_iff h₁] at h₂; exact h₂
            · decide
            · apply pos_of_ne_zero
              by_contra
              rw [this, pow_zero, totient_one] at h₂; linarith
          rw [n_exist, ha]; decide
        -- 3^b = 2
        · rcases eq_zero_or_pos b with (hb | hb)
          · rw [hb, pow_zero] at two; linarith
          · have hb' : 3 ≤ 3 ^ b := le_pow hb
            linarith
    · apply coprime_pow_primes <;> decide
  · fin_cases h' <;> decide


-- φ n ≤ 2 は n = 1, 2, 3, 4, 6 と同値
lemma totient_le_two_iff (npos : 0 < n) : φ n ≤ 2 ↔ n ∈ ({1, 2, 3, 4, 6} : Finset ℕ) := by
  constructor <;> intro h₁
  · have h₂ : n ≤ 6 := by
      interval_cases h₃ : totient n
      · linarith [totient_eq_zero.mp h₃]
      · rw [totient_eq_one_iff] at h₃; cases h₃ <;> linarith
      · rw [totient_eq_two_iff n (Ne.symm (ne_of_lt npos))] at h₃
        fin_cases h₃ <;> linarith
    interval_cases n <;> simp; contradiction
  · fin_cases h₁ <;> decide


-- 第4円分多項式 = X ^ 2 + 1
lemma cyclotomic_four : (Φ 4) = X ^ 2 + 1 := by
  have h₁ : (Φ 4) = (X^4 - 1) /ₘ ∏ i ∈ properDivisors 4, Φ i :=
    cyclotomic_eq_X_pow_sub_one_div (by decide)
  have h₂ : properDivisors 4 = {1, 2} := by decide
  have h₃ : (X - 1) * (X + 1) = (X^2 - 1 : ℚ[X]) := by ring
  rw [h₂, prod_pair (by decide), cyclotomic_one, cyclotomic_two, h₃] at h₁
  rw [h₁, divByMonic_eq_div, EuclideanDomain.div_eq_iff_eq_mul_of_dvd]
  · ring
  · exact X_pow_sub_C_ne_zero (by decide) 1
  · exact dvd_pow_sub_one_of_dvd (by decide)
  · exact monic_X_pow_sub (by norm_num)


-- 第6円分多項式 = X ^ 2 - X + 1
lemma cyclotomic_six : (Φ 6) = X ^ 2 - X + 1 := by
  have h₁ : (Φ 6) = (X^6 - 1) /ₘ ∏ i ∈ properDivisors 6, Φ i := by
      apply cyclotomic_eq_X_pow_sub_one_div (by decide)
  have h₂ : properDivisors 6 = {1, 2, 3} := by decide
  have h₃ : (X - 1) * ((X + 1) * (X^2 + X + 1)) = (X^4 + X^3 - X - 1 : ℚ[X]) := by ring
  simp [h₂, cyclotomic_one, cyclotomic_two, cyclotomic_three, h₃] at h₁
  rw [h₁, divByMonic_eq_div, EuclideanDomain.div_eq_iff_eq_mul_of_dvd]
  · ring
  · intro h
    have h_coeff := congr_arg (coeff · 4) h
    simp [coeff_X, coeff_one] at h_coeff
  · have h₄ : (X ^ 6 - 1 : ℚ[X]) = (X ^ 4 + X ^ 3 - X - 1) * (X ^ 2 - X + 1) := by ring
    rw [h₄]
    apply dvd_mul_right
  · have h : (X^4 + X^3 - X - 1 : ℚ[X]).natDegree = 4 := by
      compute_degree <;> decide
    simp [Monic, leadingCoeff, h, coeff_X, coeff_one]


-- 最小多項式のモニックな既約因子はある円分多項式と一致する
lemma normalizedfactor_class (h : IsOfFinOrder M.val) (h' : n = orderOf M.val)
    (f : ℚ[X]) (fmon : Monic f) (firr : Irreducible f) (fdvd : f ∣ minpoly ℚ M.val) :
    f ∈ ({Φ 1, Φ 2, Φ 3, Φ 4, Φ 6} : Finset ℚ[X]) := by
  obtain ⟨i, imem, feq⟩ := normalizedfactor_eq_cyclotomic M h h' f fmon firr fdvd
  rw [feq] at fdvd
  have h₁ : (Φ i).natDegree ≤ 2 :=
    calc
      _ ≤ (minpoly ℚ M.val).natDegree := natDegree_le_of_dvd fdvd (ne_zero_of_finite ℚ M.val)
      _ ≤ 2 := minpoly_deg_le_two M
  rw [cyclotomic_deg_eq_totient, totient_le_two_iff (pos_of_mem_divisors imem)] at h₁
  fin_cases h₁ <;> simp [feq]


-- 最小多項式は2乗以上の因子を持たない
lemma minpoly_squarefree (h : IsOfFinOrder M.val) (h' : n = orderOf M.val) :
    Squarefree (minpoly ℚ M.val) := by
  apply Squarefree.squarefree_of_dvd (minpoly_dvd_X_pow_sub_one M h')
  apply Separable.squarefree
  apply separable_X_pow_sub_C
  simp [h, h']; decide


-- 有限位数元の最小多項式は円分多項式で表せる
lemma minpoly_class (h : IsOfFinOrder M.val) (h' : n = orderOf M.val) :
    minpoly ℚ M.val ∈ ({Φ 1, Φ 2, Φ 3, Φ 4, Φ 6, (Φ 1)*(Φ 2)} : Finset ℚ[X]) := by
  obtain ⟨f, fmon, firr, fdvd⟩ := exist_normalizefactor M
  have h₀ := normalizedfactor_class M h h' f fmon firr fdvd
  rcases fdvd with ⟨g, fgeq⟩
  have gmon : Monic g := by
    apply Monic.of_mul_monic_left fmon
    rw [← fgeq]; exact monic (isIntegral M.val)
  have gdvd : g ∣ minpoly ℚ M.val := by
    rw [fgeq]; exact dvd_mul_left g f
  have h₃ : (minpoly ℚ M.val).natDegree = f.natDegree + g.natDegree := by
    rw [fgeq]; apply natDegree_mul (Monic.ne_zero fmon) (Monic.ne_zero gmon)
  have h₄ := minpoly_deg_le_two M
  have h₅ := minpoly_squarefree M h h'
  interval_cases h₆ : (minpoly ℚ M.val).natDegree
  -- (minpoly ℚ M.val).natDegree = 0
  · linarith [natDegree_pos (isIntegral M.val)]
  -- (minpoly ℚ M.val).natDegree = 1
  · have geq : g = 1 := by
      apply eq_one_of_monic_natDegree_zero gmon
      have : 1 ≤ f.natDegree := by
        simp only [mem_insert, mem_singleton] at h₀
        rcases h₀ with (rfl | rfl | rfl | rfl | rfl)
        <;> rw [cyclotomic_deg_eq_totient] <;> decide
      linarith
    rw [fgeq, geq, mul_one]
    simp only [mem_insert, mem_singleton] at h₀
    rcases h₀ with (rfl | rfl | rfl | rfl | rfl) <;> simp only [mem_insert, mem_singleton, true_or, or_true]
  -- (minpoly ℚ M.val).natDegree = 2
  · simp only [mem_insert, mem_singleton] at h₀
    rcases h₀ with (h1 | h1 | h1 | h1 | h1)
    -- f = Φ 1
    · have gdeg : g.natDegree = 1 := by
        have fdeg : f.natDegree = 1 := by rw [h1, cyclotomic_one]; compute_degree; decide
        rw [fdeg] at h₃; linarith
      have girr : Irreducible g := by
        apply irreducible_of_degree_eq_one
        rw [← cast_one, degree_eq_iff_natDegree_eq_of_pos (by decide)]
        exact gdeg
      simp only [mem_insert, mem_singleton]; right; right; right; right; right
      rw [fgeq, h1]
      obtain h2 := normalizedfactor_class M h h' g gmon girr gdvd
      simp only [mem_insert, mem_singleton] at h2
      rcases h2 with (h3 | h3 | h3 | h3 | h3)
      -- g = Φ 1
      · rw [h3, ← h1] at fgeq
        rw [squarefree_iff_no_irreducibles (ne_zero_of_finite ℚ M.val)] at h₅
        specialize h₅ f firr; rw [fgeq] at h₅; contrapose h₅; exact dvd_refl (f * f)
      -- g = Φ 2
      · rw [h3, cyclotomic_one, cyclotomic_two]
      -- g = Φ 3
      · rw [h3] at gdeg
        have : (X^2 + X + 1 : ℚ[X]).natDegree = 2 := by compute_degree; decide
        rw [cyclotomic_three, this] at gdeg; contradiction
      -- g = Φ 4
      · rw [h3] at gdeg
        have : (X^2 + 1 : ℚ[X]).natDegree = 2 := by compute_degree; decide
        rw [cyclotomic_four, this] at gdeg; contradiction
      -- g = Φ 6
      · rw [h3] at gdeg
        have : (X^2 - X + 1 : ℚ[X]).natDegree = 2 := by compute_degree; decide
        rw [cyclotomic_six, this] at gdeg; contradiction
    -- f = Φ 2
    · have fdeg : f.natDegree = 1 := by rw [h1, cyclotomic_two]; compute_degree; decide
      have gdeg : g.natDegree = 1 := by rw [fdeg] at h₃; linarith
      have girr : Irreducible g := by
        rw [← degree_eq_iff_natDegree_eq_of_pos (by decide), cast_one] at gdeg
        exact irreducible_of_degree_eq_one gdeg
      simp only [mem_insert, mem_singleton]; right; right; right; right; right
      rw [fgeq, h1]
      obtain h2 := normalizedfactor_class M h h' g gmon girr gdvd
      simp only [mem_insert, mem_singleton] at h2
      rcases h2 with (h3 | h3 | h3 | h3 | h3)
      -- g = Φ 1
      · rw [h3, mul_comm]
      -- g = Φ 2
      · rw [h3, ← h1] at fgeq
        rw [squarefree_iff_no_irreducibles (ne_zero_of_finite ℚ M.val)] at h₅
        specialize h₅ f firr; rw [fgeq] at h₅; contrapose h₅; exact dvd_refl (f * f)
      -- g = Φ 3
      · have : (X^2 + X + 1 : ℚ[X]).natDegree = 2 := by compute_degree; decide
        rw [h3, cyclotomic_three, this] at gdeg; contradiction
      -- g = Φ 4
      · have : (X^2 + 1 : ℚ[X]).natDegree = 2 := by compute_degree; decide
        rw [h3, cyclotomic_four, this] at gdeg; contradiction
      -- g = Φ 6
      · have : (X^2 - X + 1 : ℚ[X]).natDegree = 2 := by compute_degree; decide
        rw [h3, cyclotomic_six, this] at gdeg; contradiction
    -- f = Φ 3
    · have fdeg : f.natDegree = 2 := by rw [h1, cyclotomic_three]; compute_degree; decide
      have gdeg : g.natDegree = 0 := by rw [fdeg] at h₃; linarith
      have geq : g = 1 := eq_one_of_monic_natDegree_zero gmon gdeg
      rw [fgeq, geq, mul_one, h1]; simp only [mem_insert, mem_singleton, true_or, or_true]
    -- f = Φ 4
    · have fdeg : f.natDegree = 2 := by rw [h1, cyclotomic_four]; compute_degree; decide
      have gdeg : g.natDegree = 0 := by rw [fdeg] at h₃; linarith
      have geq : g = 1 := eq_one_of_monic_natDegree_zero gmon gdeg
      rw [fgeq, geq, mul_one, h1]; simp only [mem_insert, mem_singleton, true_or, or_true]
    -- f = Φ 6
    · have fdeg : f.natDegree = 2 := by rw [h1, cyclotomic_six]; compute_degree; decide
      have gdeg : g.natDegree = 0 := by rw [fdeg] at h₃; linarith
      have geq : g = 1 := eq_one_of_monic_natDegree_zero gmon gdeg
      rw [fgeq, geq, mul_one, h1]; simp only [mem_insert, mem_singleton, true_or, or_true]


-- 最小多項式が円分多項式で表せるとき, それは有限位数元
lemma minpoly_cyc_order (h' : n = orderOf M.val)
    (h₀ : minpoly ℚ M.val ∈ ({Φ 1, Φ 2, Φ 3, Φ 4, Φ 6, (Φ 1) * (Φ 2)} : Finset ℚ[X])) :
    n ∈ ({1, 2, 3, 4, 6} : Finset ℕ) := by
  have h_eval := aeval ℚ M.val
  simp only [mem_insert, mem_singleton]
  rw [h']; simp at h₀
  rcases h₀ with (h0 | h0 | h0 | h0 | h0 | h0) <;> rw [h0] at h_eval
  -- minpoly ℚ M.val = Φ 1
  · left; rw [orderOf_eq_one_iff]
    simp only [aeval_X, map_sub, aeval_one, sub_eq_zero] at h_eval
    exact h_eval
  -- minpoly ℚ M.val = Φ 2
  · right; left; rw [orderOf_eq_iff (by decide)]
    simp only [aeval_X, map_add, aeval_one, add_eq_zero_iff_eq_neg] at h_eval
    constructor
    · simp only [h_eval, even_two, Even.neg_pow, one_pow]
    · intro m hm mpos; interval_cases m
      rw [h_eval, pow_one]; decide
  -- minpoly ℚ M.val = Φ 3
  · right; right; left; rw [orderOf_eq_iff (by decide)]
    constructor
    · have h_poly : (X^3 - 1 : ℚ[X]) = (X - 1) * (X^2 + X + 1) := by ring
      have h_aeval_3 : aeval M.val (X^3 - 1 : ℚ[X]) = 0 := by
        rw [h_poly, map_mul, h_eval, mul_zero]
      rw [aeval_sub, map_pow, aeval_X, map_one, sub_eq_zero] at h_aeval_3
      exact h_aeval_3
    · intro m hm mpos; interval_cases m <;> intro hM
      -- m = 1
      · rw [pow_one] at hM
        simp only [hM, map_add, map_pow, aeval_X, one_pow, map_one] at h_eval
        norm_num at h_eval; contradiction
      -- m = 2
      · simp only [map_add, map_pow, aeval_X, map_one, hM] at h_eval
        rw [add_assoc, add_comm, add_assoc] at h_eval
        norm_num at h_eval
        rw [add_eq_zero_iff_eq_neg] at h_eval
        simp only [h_eval, even_two, Even.neg_pow] at hM; norm_num at hM; contradiction
  -- minpoly ℚ M.val = Φ 4
  · right; right; right; left; rw [orderOf_eq_iff (by decide)]
    constructor
    · have h_poly : (X^4 - 1 : ℚ[X]) = (X^2 + 1) * (X^2 - 1) := by ring
      have h_aeval_4 : aeval M.val (X^4 - 1 : ℚ[X]) = 0 := by
        rw [h_poly, map_mul, ← cyclotomic_four, h_eval, zero_mul]
      rw [aeval_sub, map_pow, aeval_X, map_one, sub_eq_zero] at h_aeval_4
      exact h_aeval_4
    · intro m hm mpos; interval_cases m <;> intro hM
      -- m = 1
      · rw [pow_one] at hM
        rw [cyclotomic_four, map_add, map_pow, aeval_X, map_one, hM] at h_eval
        norm_num at h_eval; contradiction
      -- m = 2
      · rw [cyclotomic_four, map_add, map_pow, aeval_X, map_one, hM] at h_eval
        norm_num at h_eval; contradiction
      -- m = 3
      · simp [cyclotomic_four, add_eq_zero_iff_eq_neg] at h_eval
        rw [pow_add M.val 1 2, h_eval, pow_one, mul_neg_one, neg_eq_iff_eq_neg] at hM
        rw [hM] at h_eval; norm_num at h_eval; contradiction
  -- minpoly ℚ M.val = Φ 6
  · right; right; right; right; rw [orderOf_eq_iff (by decide)]
    constructor
    · have h_poly : (X^6 - 1 : ℚ[X]) = (X^2 - X + 1) * (X^4 + X^3 - X - 1) := by ring
      have h_aeval_6 : aeval M.val (X^6- 1 : ℚ[X]) = 0 := by
        rw [h_poly, map_mul, ← cyclotomic_six, h_eval, zero_mul]
      rw [aeval_sub, map_pow, aeval_X, map_one, sub_eq_zero] at h_aeval_6
      exact h_aeval_6
    · intro m hm mpos; interval_cases m <;> intro hM
      -- m = 1
      · rw [pow_one] at hM
        simp [cyclotomic_six, hM] at h_eval
      -- m = 2
      · rw [cyclotomic_six, map_add, map_sub, map_pow, aeval_X, map_one] at h_eval
        rw [hM, add_comm, ← add_sub_assoc, sub_eq_zero] at h_eval; norm_num at h_eval
        rw [← h_eval] at hM; norm_num at hM; contradiction
      -- m = 3
      · rw [cyclotomic_six, map_add, map_sub, map_pow, aeval_X, map_one] at h_eval
        rw [sub_add, sub_eq_zero] at h_eval
        simp [pow_add M.val 1 2, h_eval, pow_one, mul_sub, ← pow_two] at hM
        contradiction
      -- m = 4
      · rw [cyclotomic_six, map_add, map_sub, map_pow, aeval_X, map_one] at h_eval
        rw [sub_add, sub_eq_zero] at h_eval
        rw [pow_mul M.val 2 2, h_eval, pow_two, mul_sub, sub_mul, ← pow_two] at hM
        rw [h_eval, mul_one, one_mul, sub_sub_cancel_left, neg_eq_iff_eq_neg] at hM
        rw [hM] at h_eval; norm_num at h_eval; contradiction
      -- m = 5
      · rw [cyclotomic_six, map_add, map_sub, map_pow, aeval_X, map_one] at h_eval
        rw [sub_add, sub_eq_zero] at h_eval
        rw [pow_add M.val 2 3, pow_add M.val 1 2, h_eval, pow_one, mul_sub] at hM
        rw [← pow_two, h_eval, mul_one, sub_sub_cancel_left, sub_mul, one_mul] at hM
        rw [mul_neg, mul_one, sub_neg_eq_add, add_eq_right, neg_eq_zero] at hM
        rw [hM] at h_eval; norm_num at h_eval
  -- minpoly ℚ M.val = Φ 1 * Φ 2
  · right; left; rw [orderOf_eq_iff (by decide)]
    constructor
    · rw [map_mul, map_add, map_sub, aeval_X, map_one] at h_eval
      have h₁ : (M.val - 1) * (M.val + 1) = M.val ^ 2 - 1 := by noncomm_ring
      rw [h₁] at h_eval; exact sub_eq_zero.mp h_eval
    · intro m hm mpos; interval_cases m
      rw [pow_one]; intro hM
      have M_eval : aeval M.val (X - 1 : ℚ[X]) = 0 := by simp [hM]
      have h_div : minpoly ℚ M.val ∣ (X - 1 : ℚ[X]) := dvd ℚ M.val M_eval
      rw [h0] at h_div
      have h_deg := degree_le_of_dvd h_div (X_sub_C_ne_zero 1)
      have h₁ : (X - 1 : ℚ[X]).degree = 1 := degree_X_sub_C 1
      have h₂ : (X + 1 : ℚ[X]).degree = 1 := degree_X_add_C 1
      rw [degree_mul, h₁, h₂] at h_deg; norm_num at h_deg


-- GL(2, ℚ) の有限位数は 1, 2, 3, 4, 6 に限る
theorem finorder_class (h : IsOfFinOrder M.val) (h' : n = orderOf M.val) :
    n ∈ ({1, 2, 3, 4, 6} : Finset ℕ) := by
  rcases minpoly_class M h h' with h₀
  exact minpoly_cyc_order M h' h₀

-- M(2, ℚ) ↦ GL(2, ℚ) への写像
noncomputable def toGL (A : Matrix (Fin 2) (Fin 2) ℚ) (h : IsUnit A.det) : GL (Fin 2) ℚ :=
  GeneralLinearGroup.mk'' A h

-- n = 1, 2, 3, 4, 6 それぞれに対して 位数がnとなるような代表元が存在する
theorem finite_order_matrix (h : n ∈ ({1, 2, 3, 4, 6} : Finset ℕ)) :
    ∃ (M : GL (Fin 2) ℚ), orderOf M.val = n := by
  fin_cases h
  · use 1; rw [Units.val_one, orderOf_one]
  · use toGL P1 (by simp)
    rw [toGL, GeneralLinearGroup.val_mk'', orderOf_eq_iff (by decide)]
    constructor
    · ext i j; fin_cases i <;> fin_cases j <;> simp [pow_two]
    · intro m mlt mpos; interval_cases m; rw [pow_one]; decide
  · use toGL P2 (by simp)
    rw [toGL, GeneralLinearGroup.val_mk'', orderOf_eq_iff (by decide)]
    constructor
    · ext i j; fin_cases i <;> fin_cases j <;> simp [pow_three]
    · intro m mlt mpos; interval_cases m
      · rw [pow_one]; decide
      · simp [pow_two]; decide
  · use toGL P3 (by simp)
    rw [toGL, GeneralLinearGroup.val_mk'', orderOf_eq_iff (by decide)]
    constructor
    · rw [pow_mul (!![0, 1; -1, 0]) 2 2]
      ext i j; fin_cases i <;> fin_cases j <;> simp [pow_two]
    · intro m mlt mpos; interval_cases m
      · rw [pow_one]; decide
      · simp [pow_two]; decide
      · simp [pow_three]; decide
  · use toGL P4 (by simp)
    rw [toGL, GeneralLinearGroup.val_mk'', orderOf_eq_iff (by decide)]
    constructor
    · rw [pow_mul (!![0, -1; 1, 1]) 2 3]
      ext i j; fin_cases i <;> fin_cases j <;> simp [pow_two, pow_three]
    · intro m mlt mpos; interval_cases m
      · rw [pow_one]; decide
      · simp [pow_two]; decide
      · simp [pow_three]; decide
      · rw [pow_mul (!![0, -1; 1, 1]) 2 2]
        simp [pow_two]; decide
      · rw [pow_add (!![0, -1; 1, 1]) 2 3]
        simp [pow_two, pow_three]; decide

end Nat

#min_imports
