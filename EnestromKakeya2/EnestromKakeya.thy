theory EnestromKakeya imports
  "HOL-Complex_Analysis.Complex_Analysis"
  "HOL-Computational_Algebra.Computational_Algebra"
  AutoSh
begin

section \<open>Auxiliary Lemmas\<close>

text \<open>Algebraic identity: @{term "(1 - z) * (\<Sum>k\<le>n. c k * z ^ k)"} telescopes.\<close>

lemma one_minus_z_times_sum:
  fixes c :: "nat \<Rightarrow> 'a::comm_ring_1" and z :: 'a
  shows "(1 - z) * (\<Sum>k\<le>n. c k * z ^ k) =
         c 0 + (\<Sum>k=1..n. (c k - c (k - 1)) * z ^ k) - c n * z ^ Suc n"
proof (induct n)
  case 0 show ?case by (simp add: algebra_simps)
next
  case (Suc n)
  have split: "(\<Sum>k=1..Suc n. (c k - c (k - 1)) * z ^ k) =
               (\<Sum>k=1..n. (c k - c (k - 1)) * z ^ k) + (c (Suc n) - c n) * z ^ Suc n"
    by simp
  have "(1 - z) * (\<Sum>k\<le>Suc n. c k * z ^ k) =
        (1 - z) * (\<Sum>k\<le>n. c k * z ^ k) + (c (Suc n) * z ^ Suc n - c (Suc n) * z ^ Suc (Suc n))"
    by (simp add: algebra_simps)
  also have "\<dots> = c 0 + (\<Sum>k=1..n. (c k - c (k - 1)) * z ^ k) - c n * z ^ Suc n
                 + c (Suc n) * z ^ Suc n - c (Suc n) * z ^ Suc (Suc n)"
    using Suc.hyps by (simp add: algebra_simps)
  also have "\<dots> = c 0 + (\<Sum>k=1..Suc n. (c k - c (k - 1)) * z ^ k) - c (Suc n) * z ^ Suc (Suc n)"
    using split by (simp add: algebra_simps)
  finally show ?case .
qed

lemma sum_diff_telescope:
  fixes f :: "nat \<Rightarrow> 'a::ab_group_add"
  shows "(\<Sum>k=1..n. f k - f (k - 1)) = f n - f 0"
proof (induct n)
  case 0 show ?case by simp
next
  case (Suc n) then show ?case by simp
qed

section \<open>Enestrom-Kakeya Theorem\<close>

theorem Enestrom_Kakeya:
  fixes p :: "real poly"
  assumes pos:  "coeff p 0 > 0"
  assumes mono: "\<forall>k < degree p. coeff p k \<le> coeff p (k + 1)"
  shows "\<forall>z :: complex. poly (map_poly of_real p) z = 0 \<longrightarrow> norm z \<le> 1"
proof (intro allI impI, rule ccontr)
  fix z :: complex
  assume root: "poly (map_poly of_real p) z = 0"
  assume "\<not> norm z \<le> 1"
  hence z_gt: "norm z > 1" by simp

  define n where "n = degree p"
  define a where "a k = coeff p k" for k

  have a_pos: "a 0 > 0" using pos a_def by simp

  \<comment> \<open>Degree and coefficients of the embedded complex polynomial\<close>
  have deg_mp: "degree (map_poly (of_real :: real \<Rightarrow> complex) p) = n"
    unfolding n_def by (rule degree_map_poly) simp

  have coeff_mp: "\<And>k. coeff (map_poly (of_real :: real \<Rightarrow> complex) p) k = of_real (a k)"
    by (simp add: coeff_map_poly a_def)

  \<comment> \<open>Polynomial evaluation as a finite sum\<close>
  have eval_sum: "poly (map_poly of_real p) z = (\<Sum>k\<le>n. of_real (a k) * z ^ k)"
    by (simp add: poly_altdef deg_mp coeff_mp)

  have sum_zero: "(\<Sum>k\<le>n. of_real (a k) * z ^ k) = 0"
    using root eval_sum by simp

  \<comment> \<open>The polynomial has positive degree (otherwise no root)\<close>
  have n_pos: "n > 0"
  proof (rule ccontr)
    assume "\<not> 0 < n"
    hence "n = 0" by simp
    hence "of_real (a 0) = (0::complex)" using sum_zero by simp
    thus False using a_pos by simp
  qed

  \<comment> \<open>Monotonicity and positivity of coefficients\<close>
  have a_mono: "\<And>k. k < n \<Longrightarrow> a k \<le> a (k + 1)"
    using mono n_def a_def by simp

  have a_all_pos: "\<And>k. k \<le> n \<Longrightarrow> a k > 0"
  proof -
    fix k assume "k \<le> n"
    then show "a k > 0"
    proof (induct k)
      case 0 show ?case using a_pos by simp
    next
      case (Suc k)
      hence "k < n" by simp
      hence "a k \<le> a (Suc k)" using a_mono[of k] by simp
      moreover have "a k > 0" using Suc by simp
      ultimately show ?case by simp
    qed
  qed

  have an_pos: "a n > 0" using a_all_pos by simp

  have diff_nonneg: "\<And>k. 1 \<le> k \<Longrightarrow> k \<le> n \<Longrightarrow> 0 \<le> a k - a (k - 1)"
  proof -
    fix k :: nat assume hk: "1 \<le> k" "k \<le> n"
    hence "k - 1 < n" by simp
    hence "a (k - 1) \<le> a (k - 1 + 1)" using a_mono by blast
    with hk show "0 \<le> a k - a (k - 1)" by simp
  qed

  \<comment> \<open>Key identity from multiplying the root equation by @{term "1 - z"}\<close>
  have key: "of_real (a n) * z ^ Suc n =
             of_real (a 0) + (\<Sum>k=1..n. of_real (a k - a (k - 1)) * z ^ k)"
  proof -
    note id = one_minus_z_times_sum[where c = "\<lambda>k. (of_real (a k) :: complex)" and z = z and n = n]
    from id sum_zero
    have "of_real (a 0) + (\<Sum>k=1..n. (of_real (a k) - of_real (a (k - 1))) * z ^ k)
              - of_real (a n) * z ^ Suc n = 0" by simp
    hence "of_real (a n) * z ^ Suc n =
      of_real (a 0) + (\<Sum>k=1..n. (of_real (a k) - of_real (a (k - 1))) * z ^ k)"
      by (simp add: algebra_simps)
    thus ?thesis by (simp add: of_real_diff)
  qed

  \<comment> \<open>Norm of the left-hand side\<close>
  have norm_lhs: "a n * norm z ^ Suc n =
    norm (of_real (a 0) + (\<Sum>k=1..n. of_real (a k - a (k - 1)) * z ^ k))"
  proof -
    have "norm (of_real (a n) * z ^ Suc n) = a n * norm z ^ Suc n"
      using an_pos by (simp add: norm_mult norm_power)
    moreover have "of_real (a n) * z ^ Suc n =
                   of_real (a 0) + (\<Sum>k=1..n. of_real (a k - a (k - 1)) * z ^ k)"
      by (rule key)
    ultimately show ?thesis by simp
  qed

  \<comment> \<open>Triangle inequality and norm estimates\<close>
  have "norm (of_real (a 0) + (\<Sum>k=1..n. of_real (a k - a (k - 1)) * z ^ k))
        \<le> a 0 + (\<Sum>k=1..n. (a k - a (k - 1)) * norm z ^ k)"
  proof -
    have tri: "norm (of_real (a 0) + (\<Sum>k=1..n. of_real (a k - a (k - 1)) * z ^ k)) \<le>
          norm (of_real (a 0) :: complex) +
          norm (\<Sum>k=1..n. of_real (a k - a (k - 1)) * z ^ k)"
      by (rule norm_triangle_ineq)
    have norm_a0: "norm (of_real (a 0) :: complex) = a 0"
      using a_pos by simp
    have norm_sum_le: "norm (\<Sum>k=1..n. of_real (a k - a (k - 1)) * z ^ k) \<le>
          (\<Sum>k=1..n. norm (of_real (a k - a (k - 1)) * z ^ k))"
      by (rule norm_sum)
    have norm_terms: "\<And>k. k \<in> {1..n} \<Longrightarrow>
          norm (of_real (a k - a (k - 1)) * z ^ k) = (a k - a (k - 1)) * norm z ^ k"
    proof -
      fix k :: nat assume "k \<in> {1..n}"
      hence hk: "1 \<le> k" "k \<le> n" by auto
      show "norm (of_real (a k - a (k - 1)) * z ^ k) = (a k - a (k - 1)) * norm z ^ k"
        using diff_nonneg[OF hk]
        by (simp del: of_real_diff add: norm_mult norm_power abs_of_nonneg)
    qed
    have "(\<Sum>k=1..n. norm (of_real (a k - a (k - 1)) * z ^ k)) =
          (\<Sum>k=1..n. (a k - a (k - 1)) * norm z ^ k)"
      by (intro sum.cong refl norm_terms)
    with tri norm_a0 norm_sum_le show ?thesis by linarith
  qed
  also have "\<dots> \<le> a n * norm z ^ n"
  proof -
    \<comment> \<open>Bound @{term "a 0"}: since @{term "norm z > 1"}, @{term "1 \<le> norm z ^ n"}\<close>
    have one_le: "1 \<le> norm z ^ n"
      using z_gt by (intro one_le_power) auto
    have bound_a0: "a 0 \<le> a 0 * norm z ^ n"
    proof -
      from one_le have "a 0 * 1 \<le> a 0 * norm z ^ n"
        by (intro mult_left_mono) (use a_pos in auto)
      thus ?thesis by simp
    qed
    \<comment> \<open>Bound the sum: each @{term "norm z ^ k \<le> norm z ^ n"} for @{term "k \<le> n"}\<close>
    have bound_sum: "(\<Sum>k=1..n. (a k - a (k - 1)) * norm z ^ k) \<le>
                     (\<Sum>k=1..n. (a k - a (k - 1)) * norm z ^ n)"
    proof (intro sum_mono)
      fix k assume "k \<in> {1..n}"
      hence hk: "1 \<le> k" "k \<le> n" by auto
      have "norm z ^ k \<le> norm z ^ n"
        using hk z_gt by (intro power_increasing) auto
      thus "(a k - a (k - 1)) * norm z ^ k \<le> (a k - a (k - 1)) * norm z ^ n"
        using diff_nonneg[OF hk] by (intro mult_left_mono) auto
    qed
    \<comment> \<open>Factor out @{term "norm z ^ n"} and telescope\<close>
    have "a 0 + (\<Sum>k=1..n. (a k - a (k - 1)) * norm z ^ k) \<le>
          a 0 * norm z ^ n + (\<Sum>k=1..n. (a k - a (k - 1)) * norm z ^ n)"
      using bound_a0 bound_sum by linarith
    also have "\<dots> = a 0 * norm z ^ n + (\<Sum>k=1..n. a k - a (k - 1)) * norm z ^ n"
      by (simp add: sum_distrib_right[symmetric])
    also have "\<dots> = (a 0 + (\<Sum>k=1..n. a k - a (k - 1))) * norm z ^ n"
      by (simp add: algebra_simps)
    also have "a 0 + (\<Sum>k=1..n. a k - a (k - 1)) = a n"
      using sum_diff_telescope[of a n] by simp
    finally show ?thesis by simp
  qed
  finally have ineq: "norm (of_real (a 0) + (\<Sum>k=1..n. of_real (a k - a (k - 1)) * z ^ k))
                      \<le> a n * norm z ^ n" .

  \<comment> \<open>Combine with @{thm norm_lhs} to get the key inequality\<close>
  from norm_lhs ineq have "a n * norm z ^ Suc n \<le> a n * norm z ^ n" by linarith
  hence zn: "norm z ^ Suc n \<le> norm z ^ n" using an_pos by simp
  \<comment> \<open>But @{term "norm z > 1"} means powers are strictly increasing \<longrightarrow> contradiction\<close>
  have "0 < norm z" using z_gt by linarith
  hence "norm z ^ n > 0" by (rule zero_less_power)
  with zn have "norm z ^ n * norm z \<le> norm z ^ n * 1" by simp
  with \<open>norm z ^ n > 0\<close> have "norm z \<le> 1" by simp
  with z_gt show False by simp
qed

thm Enestrom_Kakeya

end
