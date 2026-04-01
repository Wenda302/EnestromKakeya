theory EnestromKakeya imports
  "HOL-Complex_Analysis.Complex_Analysis"
  "HOL-Computational_Algebra.Computational_Algebra"
  AutoSh
begin

\<comment> \<open>Allow sorry for unfinished proofs during development\<close>
declare [[quick_and_dirty]]

text \<open>
  The Eneström–Kakeya theorem.

  Let P(z) = a_n * z^n + ... + a_1 * z + a_0 be a polynomial with real
  coefficients satisfying

      a_n \<ge> a_{n-1} \<ge> ... \<ge> a_1 \<ge> a_0 > 0.

  Then every complex root z of P satisfies |z| \<le> 1.

  Proof sketch (Rouché's theorem):
    Let f(w) = a_n * w^{n+1} and fg(w) = (w-1)*P(w), g = fg - f.
    For r > 1 and |w| = r, the key norm bound gives |g(w)| < |f(w)|.
    By Rouché on ball(0,R) with the circle of radius r:
      Σ_{zeros fg in ball} winding_number * zorder fg = Σ_{zeros f in ball} winding_number * zorder f = n+1.
    Since all zorders of fg sum to n+1 (degree), all zeros lie inside the circle of radius r.
    Taking r → 1 from above gives |z| ≤ 1.
\<close>

\<comment> \<open>
  Supporting lemma: a_n > 0.
  Since a_0 > 0 and a_0 ≤ a_1 ≤ ... ≤ a_n, we have a_n ≥ a_0 > 0.
\<close>
lemma coeff_degree_pos:
  fixes p :: "real poly"
  assumes pos:  "coeff p 0 > 0"
  assumes mono: "\<forall>k < degree p. coeff p k \<le> coeff p (k + 1)"
  shows "coeff p (degree p) > 0"
proof -
  have chain: "\<forall>k \<le> degree p. coeff p 0 \<le> coeff p k"
  proof (intro allI impI)
    fix k assume "k \<le> degree p"
    thus "coeff p 0 \<le> coeff p k"
    proof (induction k)
      case 0 show ?case by simp
    next
      case (Suc k)
      have "coeff p k \<le> coeff p (Suc k)"
        using mono Suc.prems by simp
      with Suc.IH Suc.prems show ?case by linarith
    qed
  qed
  with pos show ?thesis by force
qed

\<comment> \<open>
  Supporting lemma (sorry'd): polynomial zeros are bounded.
  Every non-zero polynomial has finitely many complex roots, hence they lie
  in some ball of radius R.
\<close>
lemma poly_zeros_bounded:
  fixes q :: "complex poly"
  assumes "q \<noteq> 0"
  obtains R :: real where "R > 0" "\<forall>u :: complex. poly q u = 0 \<longrightarrow> u \<in> ball 0 R"
proof -
  have fin: "finite {u :: complex. poly q u = 0}"
    by (rule poly_roots_finite[OF assms])
  define M where "M = Max (insert 1 (norm ` {u :: complex. poly q u = 0}))"
  have hfin: "finite (insert 1 (norm ` {u :: complex. poly q u = 0}))"
    by (simp add: fin)
  have hM_ge: "1 \<le> M"
    unfolding M_def by (intro Max_ge hfin) simp
  show ?thesis
  proof (rule that[of "M + 1"])
    show "M + 1 > 0" using hM_ge by linarith
    show "\<forall>u :: complex. poly q u = 0 \<longrightarrow> u \<in> ball 0 (M + 1)"
    proof (intro allI impI)
      fix u assume hu: "poly q u = 0"
      have "norm u \<le> M"
        unfolding M_def
        by (intro Max_ge hfin) (simp add: imageI hu)
      thus "u \<in> ball 0 (M + 1)"
        by (simp add: ball_def dist_0_norm)
    qed
  qed
qed

\<comment> \<open>
  Key norm bound on the circle of radius r > 1.
  For p with 0 < a_0 ≤ a_1 ≤ ... ≤ a_n, for each degree n,
  stripping the leading term reduces n by 1 while preserving conditions.
\<close>
lemma norm_bound_key:
  fixes r :: real and w :: complex
  assumes hr: "1 < r" and hw: "norm w = r"
  shows "degree p = n \<Longrightarrow> coeff p 0 > 0 \<Longrightarrow>
          (\<forall>k < n. coeff p k \<le> coeff p (k + 1)) \<Longrightarrow>
          cmod ((w - 1) * poly (map_poly of_real p) w - of_real (coeff p n) * w ^ (n + 1))
          < coeff p n * r ^ (n + 1)"
proof (induction n arbitrary: p)
  case (0 p)
  have hdeg: "degree p = 0" using "0.prems"(1) .
  have hpos0: "coeff p 0 > 0" using "0.prems"(2) .
  \<comment> \<open>degree 0: poly p w = coeff p 0\<close>
  have poly_val: "poly (map_poly of_real p) w = of_real (coeff p 0)"
  proof -
    have hdeg': "degree (map_poly (of_real :: real \<Rightarrow> complex) p) = 0"
    proof (rule le_antisym)
      show "degree (map_poly (of_real :: real \<Rightarrow> complex) p) \<le> 0"
        by (rule degree_le) (simp add: coeff_map_poly coeff_eq_0 hdeg)
      show "0 \<le> degree (map_poly (of_real :: real \<Rightarrow> complex) p)" by simp
    qed
    have "poly (map_poly (of_real :: real \<Rightarrow> complex) p) w
          = coeff (map_poly (of_real :: real \<Rightarrow> complex) p) 0"
      by (simp add: poly_altdef hdeg')
    also have "\<dots> = of_real (coeff p 0)"
      by (simp add: coeff_map_poly)
    finally show ?thesis .
  qed
  have lhs_val: "(w - 1) * poly (map_poly of_real p) w - of_real (coeff p 0) * w ^ 1
                 = -of_real (coeff p 0)"
    by (simp add: poly_val ring_distribs)
  show ?case
  proof -
    have lhs_eq: "cmod ((w - 1) * poly (map_poly of_real p) w
                        - of_real (coeff p 0) * w ^ (0 + 1)) = coeff p 0"
      by (simp add: poly_val ring_distribs norm_minus_cancel norm_of_real abs_of_pos hpos0)
    have rhs_eq: "coeff p 0 * r ^ (0 + 1) = coeff p 0 * r" by simp
    have bound: "coeff p 0 < coeff p 0 * r"
      using mult_strict_left_mono[OF hr hpos0] by simp
    show ?thesis using lhs_eq rhs_eq bound by linarith
  qed
next
  case (Suc n p)
  have hdeg: "degree p = Suc n" using "Suc.prems"(1) .
  have hpos0: "coeff p 0 > 0" using "Suc.prems"(2) .
  have hmono: "\<forall>k < Suc n. coeff p k \<le> coeff p (k + 1)" using "Suc.prems"(3) .
  let ?an = "coeff p (Suc n)"
  let ?p' = "p - monom ?an (Suc n)"
  \<comment> \<open>Step 1: degree p' = n\<close>
  have coeff_p'_n: "coeff ?p' n = coeff p n"
    by (simp add: coeff_diff coeff_monom)
  have hpn_pos: "coeff p n > 0"
  proof -
    have chain: "\<forall>m \<le> n. coeff p 0 \<le> coeff p m"
    proof (intro allI impI)
      fix m :: nat assume hm: "m \<le> n"
      show "coeff p 0 \<le> coeff p m"
        using hm
      proof (induction m)
        case 0 show ?case by simp
      next
        case (Suc k)
        have hk_lt: "k < Suc n" using "Suc.prems" by linarith
        have step: "coeff p k \<le> coeff p (Suc k)" using hmono hk_lt by simp
        have ih: "coeff p 0 \<le> coeff p k" using "Suc.IH" "Suc.prems" by linarith
        show ?case using step ih by linarith
      qed
    qed
    have "coeff p 0 \<le> coeff p n" using chain by simp
    with hpos0 show ?thesis by linarith
  qed
  have coeff_p'_vanish: "\<forall>k > n. coeff ?p' k = 0"
  proof (intro allI impI)
    fix k :: nat
    assume hk: "n < k"
    show "coeff ?p' k = 0"
    proof (cases "k = Suc n")
      case True
      show ?thesis using True by (simp add: coeff_diff coeff_monom)
    next
      case False
      then have hlt: "Suc n < k" using hk by auto
      have hdegk: "degree p < k" using hdeg hlt by linarith
      have hpk: "coeff p k = 0" using hdegk by (rule coeff_eq_0)
      have hmonk: "coeff (monom ?an (Suc n)) k = 0" using hlt by (auto simp: coeff_monom)
      show ?thesis using hpk hmonk by (simp add: coeff_diff)
    qed
  qed
  have hdeg': "degree ?p' = n"
  proof (rule antisym)
    show "degree ?p' \<le> n" using coeff_p'_vanish by (rule degree_le)
    show "n \<le> degree ?p'"
    proof (rule le_degree)
      have "coeff ?p' n = coeff p n" using coeff_p'_n .
      thus "coeff ?p' n \<noteq> 0" using hpn_pos by linarith
    qed
  qed
  \<comment> \<open>Step 2: p' satisfies the positivity and mono conditions\<close>
  have hpos': "coeff ?p' 0 > 0"
    by (simp add: coeff_diff coeff_monom hpos0)
  have hmono': "\<forall>k < n. coeff ?p' k \<le> coeff ?p' (k + 1)"
  proof (intro allI impI)
    fix k assume hk: "k < n"
    have eq_k: "coeff ?p' k = coeff p k"
      using hk by (auto simp: coeff_diff coeff_monom)
    have eq_k1: "coeff ?p' (k + 1) = coeff p (k + 1)"
      using hk by (auto simp: coeff_diff coeff_monom)
    show "coeff ?p' k \<le> coeff ?p' (k + 1)"
      using hmono hk eq_k eq_k1 by simp
  qed
  \<comment> \<open>Step 3: Apply IH to p'\<close>
  have ih: "cmod ((w - 1) * poly (map_poly of_real ?p') w - of_real (coeff p n) * w ^ (n + 1))
            < coeff p n * r ^ (n + 1)"
    using Suc.IH[of ?p', OF hdeg' hpos' hmono'] coeff_p'_n by simp
  \<comment> \<open>Step 4: Algebraic identity\<close>
  have poly_p': "poly (map_poly of_real ?p') w =
                 poly (map_poly of_real p) w - of_real ?an * w ^ (Suc n)"
  proof -
    have "map_poly (of_real :: real \<Rightarrow> complex) ?p' =
          map_poly (of_real :: real \<Rightarrow> complex) p - monom ((of_real :: real \<Rightarrow> complex) ?an) (Suc n)"
      by (intro poly_eqI) (simp add: coeff_map_poly coeff_diff coeff_monom)
    thus ?thesis by (simp add: poly_diff poly_monom)
  qed
  have identity: "(w - 1) * poly (map_poly of_real p) w - of_real ?an * w ^ (Suc n + 1) =
                 (w - 1) * poly (map_poly of_real ?p') w - of_real ?an * w ^ (Suc n)"
    by (simp add: poly_p' algebra_simps power_Suc)
  \<comment> \<open>Step 5: Bound via IH + triangle inequality\<close>
  have an_ge_n: "coeff p n \<le> ?an" using hmono by simp
  have diff_neg: "coeff p n - ?an \<le> 0" using an_ge_n by linarith
  have diff_cmod: "cmod (of_real (coeff p n - ?an) * w ^ (Suc n)) = (?an - coeff p n) * r ^ (Suc n)"
    by (simp del: of_real_diff add: norm_mult norm_of_real abs_of_nonpos[OF diff_neg] norm_power hw)
  have split_it: "(w - 1) * poly (map_poly of_real ?p') w - of_real ?an * w ^ (Suc n) =
                 ((w - 1) * poly (map_poly of_real ?p') w - of_real (coeff p n) * w ^ (Suc n))
                 + of_real (coeff p n - ?an) * w ^ (Suc n)"
    by (simp add: of_real_diff algebra_simps)
  have main_bound: "cmod ((w - 1) * poly (map_poly of_real p) w - of_real ?an * w ^ (Suc n + 1))
                    < ?an * r ^ (Suc n)"
  proof -
    have "cmod ((w - 1) * poly (map_poly of_real p) w - of_real ?an * w ^ (Suc n + 1))
          = cmod ((w - 1) * poly (map_poly of_real ?p') w - of_real ?an * w ^ (Suc n))"
      by (simp only: identity)
    also have "\<dots> = cmod (((w - 1) * poly (map_poly of_real ?p') w
                            - of_real (coeff p n) * w ^ (Suc n))
                          + of_real (coeff p n - ?an) * w ^ (Suc n))"
      by (simp only: split_it)
    also have "\<dots> \<le> cmod ((w - 1) * poly (map_poly of_real ?p') w
                            - of_real (coeff p n) * w ^ (Suc n))
                     + cmod (of_real (coeff p n - ?an) * w ^ (Suc n))"
      by (rule norm_triangle_ineq)
    also have "\<dots> < coeff p n * r ^ (Suc n) + (?an - coeff p n) * r ^ (Suc n)"
    proof -
      have suc_eq: "Suc n = n + 1" by simp
      show ?thesis using ih diff_cmod by (simp only: suc_eq)
    qed
    also have "\<dots> = ?an * r ^ (Suc n)" by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  \<comment> \<open>Step 6: an * r^n < an * r^(n+1)\<close>
  have an_pos: "(0 :: real) < ?an"
    using hpn_pos an_ge_n by linarith
  have strict: "?an * r ^ (Suc n) < ?an * r ^ (Suc n + 1)"
    using an_pos hr by (simp add: power_Suc mult_less_cancel_left_pos)
  show ?case using main_bound strict by linarith
qed

lemma norm_bound_on_circle:
  fixes p :: "real poly"
  assumes pos:  "coeff p 0 > 0"
  assumes mono: "\<forall>k < degree p. coeff p k \<le> coeff p (k + 1)"
  assumes hr:   "1 < r"
  assumes hw:   "norm w = r"
  shows "cmod ((w - 1) * poly (map_poly of_real p) w
               - of_real (coeff p (degree p)) * w ^ (degree p + 1))
         < cmod (of_real (coeff p (degree p)) * w ^ (degree p + 1))"
proof -
  have an_pos: "0 < coeff p (degree p)"
    using coeff_degree_pos[OF pos mono] .
  have rhs_eq: "cmod (of_real (coeff p (degree p)) * w ^ (degree p + 1)) =
                coeff p (degree p) * r ^ (degree p + 1)"
    by (simp add: norm_mult norm_of_real abs_of_pos an_pos norm_power hw)
  have lhs_bound: "cmod ((w - 1) * poly (map_poly of_real p) w
                         - of_real (coeff p (degree p)) * w ^ (degree p + 1))
                   < coeff p (degree p) * r ^ (degree p + 1)"
  proof (rule norm_bound_key[OF hr hw])
      show "degree p = degree p" by simp
      show "0 < coeff p 0" using pos .
      show "\<forall>k<degree p. coeff p k \<le> coeff p (k + 1)" using mono .
    qed
  show ?thesis using lhs_bound rhs_eq by simp
qed

\<comment> \<open>
  Supporting lemma (sorry'd): zorder of a_n*w^{n+1} at 0 is n+1.
\<close>
lemma zorder_monomial:
  assumes "an \<noteq> (0 :: complex)"
  shows "zorder (\<lambda>w :: complex. an * w ^ (n + 1)) 0 = int (n + 1)"
  apply (rule zorder_eqI[where g = "\<lambda>_. an" and S = UNIV and n = "int (n + 1)"])
     apply simp
     apply simp
     apply (intro holomorphic_intros)
     apply (simp add: assms)
     apply (simp only: diff_zero power_int_of_nat)
  done

\<comment> \<open>
  Supporting lemma (sorry'd): winding number of circlepath 0 r around an interior point is 1.
\<close>
lemma winding_number_circlepath_interior:
  assumes "r > 0" "norm w < r"
  shows "winding_number (circlepath 0 r) w = 1"
  using winding_number_circlepath[of w 0 r] assms by simp

\<comment> \<open>
  Supporting lemma (sorry'd): sum of zorders of a complex polynomial over all zeros = degree.
  (Fundamental theorem of algebra / algebraic closure of ℂ.)
\<close>
lemma sum_zorder_eq_degree:
  fixes q :: "complex poly"
  assumes hq: "q \<noteq> 0"
  shows "(\<Sum>u \<in> {u. poly q u = 0}. zorder (poly q) u) = int (degree q)"
proof -
  \<comment> \<open>Step 1: zorder (poly q) a = int (order a q) for each root a.\<close>
  have zorder_eq_order: "\<And>a :: complex. poly q a = 0 \<Longrightarrow> zorder (poly q) a = int (order a q)"
  proof -
    fix a :: complex assume ha: "poly q a = 0"
    from order_decomp[OF hq, of a] obtain r where
      hr: "q = [:-a, 1:] ^ order a q * r" and hndvd: "\<not> [:-a, 1:] dvd r"
      by blast
    have hr_nz: "poly r a \<noteq> 0"
      using hndvd by (simp add: poly_eq_0_iff_dvd)
    show "zorder (poly q) a = int (order a q)"
    proof (rule zorder_eqI[where g = "poly r" and S = UNIV and n = "int (order a q)"])
      show "open (UNIV :: complex set)" by simp
      show "a \<in> (UNIV :: complex set)" by simp
      show "poly r holomorphic_on UNIV"
        unfolding poly_altdef by (intro holomorphic_intros)
      show "poly r a \<noteq> 0" by (fact hr_nz)
      \<comment> \<open>First expand: poly q w = (w-a)^n * poly r w.
          Use subst (1) hr to rewrite only poly q w, not q inside order a q.\<close>
      have poly_eq: "\<And>w :: complex. poly q w = (w - a) ^ order a q * poly r w"
      proof -
        fix w :: complex
        have step1 : "poly q w = poly ([:-a, 1:] ^ order a q * r) w"
          by (subst (1) hr, rule refl)
        have step2 : "poly ([:-a, 1:] ^ order a q * r) w = (w - a) ^ order a q * poly r w"
          by (simp add: poly_mult poly_power)
        show "poly q w = (w - a) ^ order a q * poly r w"
          using step1 step2 by simp
      qed
      show "\<And>w. w \<in> (UNIV :: complex set) \<Longrightarrow> w \<noteq> a \<Longrightarrow>
              poly q w = poly r w * (w - a) powi int (order a q)"
        by (simp only: poly_eq power_int_of_nat ac_simps)
    qed
  qed
  \<comment> \<open>Step 2: sum of algebraic orders = degree, via complex_poly_decompose.\<close>
  have sum_order_eq: "(\<Sum>a | poly q a = 0. order a q) = degree q"
  proof -
    have decomp: "smult (lead_coeff q) (\<Prod>z | poly q z = 0. [:-z, 1:] ^ order z q) = q"
      by (rule complex_poly_decompose)
    have lead_nz: "lead_coeff q \<noteq> 0" using hq by simp
    have "degree q = degree (\<Prod>z | poly q z = 0. [:-z, 1:] ^ order z q)"
      by (metis decomp degree_smult_eq lead_nz)
    also have "\<dots> = (\<Sum>z | poly q z = 0. degree ([:-z, 1:] ^ order z q))"
      by (rule degree_prod_eq_sum_degree) simp
    also have "\<dots> = (\<Sum>z | poly q z = 0. order z q)"
      by (rule sum.cong) (auto simp: degree_linear_power)
    finally show ?thesis by simp
  qed
  \<comment> \<open>Combine.\<close>
  have "(\<Sum>u \<in> {u. poly q u = 0}. zorder (poly q) u) =
        (\<Sum>u \<in> {u. poly q u = 0}. int (order u q))"
    by (rule sum.cong) (auto simp: zorder_eq_order)
  also have "\<dots> = int (\<Sum>u \<in> {u. poly q u = 0}. order u q)"
    by (simp only: of_nat_sum [symmetric])
  also have "\<dots> = int (degree q)"
    using sum_order_eq by simp
  finally show ?thesis .
qed

\<comment> \<open>
  Supporting lemma (sorry'd):
  zorder fg w ≥ 1 whenever fg w = 0.
\<close>
lemma zorder_pos_at_zero:
  fixes fg :: "complex \<Rightarrow> complex"
  assumes "fg w = 0" "fg analytic_on {w}"
  assumes "\<exists>\<^sub>F z in nhds w. fg z \<noteq> 0"
  shows "1 \<le> zorder fg w"
proof -
  have freq: "\<exists>\<^sub>F z in at w. fg z \<noteq> 0"
  proof (rule ccontr)
    assume "\<not> (\<exists>\<^sub>F z in at w. fg z \<noteq> 0)"
    hence "eventually (\<lambda>z. fg z = 0) (nhds w)"
      using assms(1) by (simp add: frequently_def eventually_nhds_conv_at)
    with assms(3) show False by (simp add: frequently_def)
  qed
  have "0 < zorder fg w"
    using zorder_pos_iff'[OF assms(2) freq] assms(1) by simp
  thus ?thesis by simp
qed

theorem Enestrom_Kakeya:
  fixes p :: "real poly"
  assumes pos:  "coeff p 0 > 0"
  assumes mono: "\<forall>k < degree p. coeff p k \<le> coeff p (k + 1)"
  shows "\<forall>z :: complex. poly (map_poly of_real p) z = 0 \<longrightarrow> norm z \<le> 1"
proof (intro allI impI)
  fix z :: complex
  assume hz : "poly (map_poly of_real p) z = 0"

  let ?n   = "degree p"
  let ?cp  = "map_poly of_real p :: complex poly"
  let ?an  = "coeff p ?n"
  \<comment> \<open>f(w) = a_n * w^{n+1}, the "dominant" monomial\<close>
  let ?f   = "\<lambda>w :: complex. of_real ?an * w ^ (?n + 1)"
  \<comment> \<open>fg(w) = (w-1)*P(w); a zero of P is a zero of fg\<close>
  let ?fg  = "\<lambda>w :: complex. (w - 1) * poly ?cp w"
  \<comment> \<open>g = fg - f, so f + g = fg\<close>
  let ?g   = "\<lambda>w :: complex. ?fg w - ?f w"

  have hfgz : "?fg z = 0"
    by (simp add: hz)

  have pos_an : "(0 :: real) < ?an"
    using coeff_degree_pos[OF pos mono] .

  \<comment> \<open>Main claim: for every r > 1, every zero of ?fg has norm < r.\<close>
  have zeros_in_ball : "\<forall>r > (1::real). \<forall>w :: complex. ?fg w = 0 \<longrightarrow> norm w < r"
  proof (intro allI impI)
    fix r :: real and w :: complex
    assume hr  : "1 < r"
    assume hfw : "?fg w = 0"
    show "norm w < r"
    proof (rule ccontr)
      assume hn : "\<not> norm w < r"
      hence hnr : "r \<le> norm w" by simp

      \<comment> \<open>Choose R > r containing all zeros of ?fg.\<close>
      have cp_nz : "?cp \<noteq> 0" 
      \<comment> \<open>Since ?fg is the evaluation of a non-zero polynomial, its zeros are finite and bounded.\<close>
        by (metis coeff_0 coeff_map_poly of_real_eq_0_iff order_less_irrefl
            pos)
      obtain R :: real where hR_pos : "0 < R" and hRr : "r < R"
        and hR : "\<forall>u :: complex. ?fg u = 0 \<longrightarrow> u \<in> ball 0 R"
      proof -
        have nz: "[:-1,1:] * ?cp \<noteq> (0 :: complex poly)"
          by (metis cp_nz mult_eq_0_iff pCons_eq_0_iff zero_neq_one)
        obtain R0 where hR0_pos: "0 < R0"
          and hR0: "\<forall>u :: complex. poly ([:-1,1:] * ?cp) u = 0 \<longrightarrow> u \<in> ball 0 R0"
          by (rule poly_zeros_bounded[OF nz])
        show ?thesis
        proof (rule that[of "max R0 r + 1"])
          show "0 < max R0 r + 1" using hr by linarith
          show "r < max R0 r + 1" by linarith
          show "\<forall>u :: complex. ?fg u = 0 \<longrightarrow> u \<in> ball 0 (max R0 r + 1)"
          proof (intro allI impI)
            fix u assume hfu: "?fg u = 0"
            have "poly ([:-1,1:] * ?cp) u = 0"
              using hfu by (auto simp: poly_mult algebra_simps)
            hence "u \<in> ball 0 R0" using hR0 by blast
            thus "u \<in> ball 0 (max R0 r + 1)"
              by (simp add: ball_def dist_0_norm)
          qed
        qed
      qed

      let ?s     = "ball (0 :: complex) R"
      let ?gamma = "circlepath (0 :: complex) r"
      let ?zf    = "{q \<in> ?s. ?f  q = 0}"
      let ?zfg   = "{q \<in> ?s. ?fg q = 0}"

      \<comment> \<open>zeros_f = {0} since f(w) = a_n*w^{n+1} with a_n > 0.\<close>
      have hzf : "?zf = {0}"
        using hR_pos pos_an
        by (auto simp: ball_def power_eq_0_iff of_real_eq_0_iff)

      \<comment> \<open>zeros_fg = all zeros of ?fg (since all fit inside ball 0 R).\<close>
      have hzfg : "?zfg = {u. ?fg u = 0}"
        using hR by (auto simp: ball_def)

      \<comment> \<open>w belongs to ?zfg.\<close>
      have hw_in : "w \<in> ?zfg"
        using hfw hR by blast

      \<comment> \<open>Note: ?f w + ?g w = ?fg w by definition of ?g = ?fg - ?f.\<close>
      have fg_sum_eq : "(\<lambda>w :: complex. ?f w + ?g w) = ?fg"
        by (simp add: algebra_simps fun_eq_iff)

      \<comment> \<open>Apply Rouché's theorem.\<close>
      have rouche_raw :
        "(\<Sum>q \<in> {q \<in> ?s. ?f q + ?g q = 0}.
            winding_number ?gamma q * zorder (\<lambda>w. ?f w + ?g w) q) =
         (\<Sum>q \<in> ?zf. winding_number ?gamma q * zorder ?f q)"
      proof (rule Rouche_theorem [where f = ?f and g = ?g and s = ?s and \<gamma> = ?gamma])
        show "open ?s"      by simp
        show "connected ?s" by (simp add: convex_connected)
        show "finite {q \<in> ?s. ?f q + ?g q = 0}"
        proof -
          have sub: "{q \<in> ?s. ?f q + ?g q = 0} \<subseteq> {q. poly ([:-1,1:] * ?cp) q = 0}"
            by (auto simp: fg_sum_eq algebra_simps poly_mult)
          have nz: "[:-1,1:] * ?cp \<noteq> (0 :: complex poly)"
            by (metis cp_nz mult_eq_0_iff pCons_eq_0_iff zero_neq_one)
          have "finite {q. poly ([:-1,1:] * ?cp) q = 0}"
            by (intro poly_roots_finite nz)
          from finite_subset[OF sub this] show ?thesis .
        qed
        show "finite ?zf"   unfolding hzf by simp
        show "?f holomorphic_on ?s" by (intro holomorphic_intros)
        show "?g holomorphic_on ?s"
          unfolding fg_sum_eq[symmetric]
          by (intro holomorphic_intros)
        show "valid_path ?gamma"   by simp
        show "pathfinish ?gamma = pathstart ?gamma" by simp
        show "path_image ?gamma \<subseteq> ?s"
          using hRr hr
          by (auto simp: path_image_circlepath sphere_def dist_commute abs_of_pos)
        show "\<forall>q \<in> path_image ?gamma. cmod (?f q) > cmod (?g q)"
          using norm_bound_on_circle[OF pos mono hr] hr
          by (auto simp: path_image_circlepath sphere_def power_Suc abs_of_pos)
        show "\<forall>q. q \<notin> ?s \<longrightarrow> winding_number ?gamma q = 0"
        proof (intro allI impI)
          fix q assume "q \<notin> ?s"
          show "winding_number ?gamma q = 0"
            by (rule winding_number_zero_outside[where s = "ball 0 R"])
               (use hRr hr \<open>q \<notin> ?s\<close> in
                \<open>auto simp: path_image_circlepath sphere_def abs_of_pos\<close>)
        qed
      qed

      \<comment> \<open>Convert: replace f+g with ?fg throughout.\<close>
      have rouche :
        "(\<Sum>q \<in> ?zfg. winding_number ?gamma q * zorder ?fg q) =
         (\<Sum>q \<in> ?zf.  winding_number ?gamma q * zorder ?f  q)"
        using rouche_raw fg_sum_eq by simp

      \<comment> \<open>The RHS evaluates to n+1.\<close>
      have rhs_val :
        "(\<Sum>q \<in> ?zf. winding_number ?gamma q * zorder ?f q) = of_nat (?n + 1)"
      proof -
        have "(\<Sum>q \<in> ?zf. winding_number ?gamma q * zorder ?f q) =
              winding_number ?gamma 0 * zorder ?f 0"
          by (subst hzf, simp)
        also have "winding_number ?gamma 0 = 1"
          using winding_number_circlepath_interior[of r 0] hr by simp
        also have "zorder ?f 0 = int (?n + 1)"
        proof (rule zorder_monomial)
          show "of_real ?an \<noteq> (0 :: complex)"
            using pos_an by (auto simp: of_real_eq_0_iff)
        qed
        finally show ?thesis by simp
      qed

      \<comment> \<open>Sum of all zorders of ?fg = degree of (w-1)*P(w) = n+1 (FTA).\<close>
      have total :
        "(\<Sum>u \<in> {u. ?fg u = 0}. zorder ?fg u) = int (?n + 1)"
      proof -
        have nz_prod: "[:-1,1:] * ?cp \<noteq> (0 :: complex poly)"
          by (metis cp_nz mult_eq_0_iff pCons_eq_0_iff zero_neq_one)
        have fg_eq: "?fg = poly ([:-1,1:] * ?cp)"
          by (simp add: poly_mult fun_eq_iff algebra_simps)
        have deg_eq: "degree ([:-1,1:] * ?cp) = ?n + 1"
        proof -
          have "degree ([:-1,1:] * ?cp) = degree ([:-1,1:] :: complex poly) + degree ?cp"
            by (rule degree_mult_eq) (use nz_prod cp_nz in auto)
          also have "degree ([:-1,1:] :: complex poly) = 1" by simp
          also have "degree ?cp = ?n"
            by (rule degree_map_poly) (simp add: of_real_eq_0_iff)
          finally show ?thesis by simp
        qed
        have "(\<Sum>u \<in> {u. ?fg u = 0}. zorder ?fg u) =
              (\<Sum>u \<in> {u. poly ([:-1,1:] * ?cp) u = 0}. zorder (poly ([:-1,1:] * ?cp)) u)"
        proof (rule sum.cong)
          show "{u :: complex. ?fg u = 0} = {u. poly ([:-1,1:] * ?cp) u = 0}"
            using fg_eq by auto
          fix u assume _: "u \<in> {u. poly ([:-1,1:] * ?cp) u = 0}"
          show "zorder ?fg u = zorder (poly ([:-1,1:] * ?cp)) u"
            using fg_eq by simp
        qed
        also have "\<dots> = int (degree ([:-1,1:] * ?cp))"
          by (rule sum_zorder_eq_degree[OF nz_prod])
        also have "\<dots> = int (?n + 1)"
          by (simp only: deg_eq)
        finally show ?thesis .
      qed

      \<comment> \<open>Winding number = 1 for zeros inside circle (norm < r).\<close>
      have winding_1 : "\<forall>q \<in> ?zfg. norm q < r \<longrightarrow> winding_number ?gamma q = 1"
        using winding_number_circlepath_interior[of r] hr
        by (auto simp: ball_def)

      \<comment> \<open>Winding number = 0 for zeros outside/on circle.\<close>
      have winding_0 : "\<forall>q \<in> ?zfg. r \<le> norm q \<longrightarrow> winding_number ?gamma q = 0"
      proof (intro ballI impI)
        fix q assume hq_mem: "q \<in> ?zfg" and hnq: "r \<le> norm q"
        have hfgq: "?fg q = 0"
          using hq_mem hzfg by auto
        have q_ne_r: "norm q \<noteq> r"
        proof
          assume heq: "norm q = r"
          have hbound: "cmod (?g q) < cmod (?f q)"
            using norm_bound_on_circle[OF pos mono hr] heq by simp
          have hne: "?f q + ?g q \<noteq> 0"
          proof
            assume h: "?f q + ?g q = 0"
            hence "cmod (?g q) = cmod (?f q)"
              by (metis add_eq_0_iff norm_minus_cancel)
            with hbound show False by linarith
          qed
          have "?f q + ?g q = 0"
            by (metis fg_sum_eq hfgq fun_eq_iff)
          with hne show False by contradiction
        qed
        have hq_out: "r < norm q" using hnq q_ne_r by linarith
        show "winding_number ?gamma q = 0"
          by (rule winding_number_zero_outside[where s = "cball 0 r"])
             (use hq_out hr in \<open>auto simp: path_image_circlepath sphere_def dist_0_norm\<close>)
      qed

      \<comment> \<open>Zeros of ?fg are finite (needed below).\<close>
      have fin_zfg : "finite ?zfg"
      proof -
        have nz': "[:-1,1:] * ?cp \<noteq> (0 :: complex poly)"
          by (metis cp_nz mult_eq_0_iff pCons_eq_0_iff zero_neq_one)
        have sub: "?zfg \<subseteq> {u. poly ([:-1,1:] * ?cp) u = 0}"
          using hzfg by (auto simp: poly_mult algebra_simps)
        from finite_subset[OF sub poly_roots_finite[OF nz']] show ?thesis .
      qed

      \<comment> \<open>Rewrite LHS: only inside zeros contribute (outside get weight 0).\<close>
      have lhs_split :
        "(\<Sum>q \<in> ?zfg. winding_number ?gamma q * zorder ?fg q) =
         of_int (\<Sum>q \<in> {q \<in> ?zfg. norm q < r}. zorder ?fg q)"
      proof -
        have fin1: "finite {q \<in> ?zfg. norm q < r}"
          by (rule finite_subset[OF _ fin_zfg]) auto
        have fin2: "finite {q \<in> ?zfg. r \<le> norm q}"
          by (rule finite_subset[OF _ fin_zfg]) auto
        have eq: "?zfg = {q \<in> ?zfg. norm q < r} \<union> {q \<in> ?zfg. r \<le> norm q}" by auto
        have "(\<Sum>q \<in> ?zfg. winding_number ?gamma q * zorder ?fg q) =
              (\<Sum>q \<in> {q \<in> ?zfg. norm q < r}. winding_number ?gamma q * zorder ?fg q) +
              (\<Sum>q \<in> {q \<in> ?zfg. r \<le> norm q}. winding_number ?gamma q * zorder ?fg q)"
          by (subst eq, rule sum.union_disjoint[OF fin1 fin2]) auto
        also have "(\<Sum>q \<in> {q \<in> ?zfg. norm q < r}. winding_number ?gamma q * zorder ?fg q) =
                   of_int (\<Sum>q \<in> {q \<in> ?zfg. norm q < r}. zorder ?fg q)"
        proof -
          have "(\<Sum>q \<in> {q \<in> ?zfg. norm q < r}. winding_number ?gamma q * zorder ?fg q) =
                (\<Sum>q \<in> {q \<in> ?zfg. norm q < r}. of_int (zorder ?fg q))"
            by (rule sum.cong) (use winding_1 in auto)
          also have "\<dots> = of_int (\<Sum>q \<in> {q \<in> ?zfg. norm q < r}. zorder ?fg q)"
            by (simp add: of_int_sum)
          finally show ?thesis .
        qed
        also have "(\<Sum>q \<in> {q \<in> ?zfg. r \<le> norm q}. winding_number ?gamma q * zorder ?fg q) = 0"
          by (rule sum.neutral) (use winding_0 in auto)
        finally show ?thesis by simp
      qed

      \<comment> \<open>From Rouché + RHS: inside sum of zorders = n+1 (as integers).\<close>
      have inside_eq :
        "(\<Sum>q \<in> {q \<in> ?zfg. norm q < r}. zorder ?fg q) = int (?n + 1)"
      proof -
        have h1: "of_int (\<Sum>q \<in> {q \<in> ?zfg. norm q < r}. zorder ?fg q) =
                  (of_nat (?n + 1) :: complex)"
          using rouche rhs_val lhs_split by simp
        have h2: "(of_nat (?n + 1) :: complex) = of_int (int (?n + 1))"
          by (rule of_int_of_nat_eq [symmetric])
        from h1 h2 have "of_int (\<Sum>q \<in> {q \<in> ?zfg. norm q < r}. zorder ?fg q) =
                         (of_int (int (?n + 1)) :: complex)"
          by simp
        thus ?thesis by (simp only: of_int_eq_iff)
      qed

      \<comment> \<open>Total sum = inside + outside (split the finite sum).\<close>
      have sum_split :
        "(\<Sum>q \<in> ?zfg. zorder ?fg q) =
         (\<Sum>q \<in> {q \<in> ?zfg. norm q < r}. zorder ?fg q) +
         (\<Sum>q \<in> {q \<in> ?zfg. r \<le> norm q}. zorder ?fg q)"
      proof -
        have fin1: "finite {q \<in> ?zfg. norm q < r}"
          by (rule finite_subset[OF _ fin_zfg]) auto
        have fin2: "finite {q \<in> ?zfg. r \<le> norm q}"
          by (rule finite_subset[OF _ fin_zfg]) auto
        have eq: "?zfg = {q \<in> ?zfg. norm q < r} \<union> {q \<in> ?zfg. r \<le> norm q}"
          by auto
        show ?thesis
          by (subst eq, rule sum.union_disjoint) (use fin1 fin2 in auto)
      qed

      \<comment> \<open>So outside sum = 0 (as integers).\<close>
      have outside_zero :
        "(\<Sum>q \<in> {q \<in> ?zfg. r \<le> norm q}. zorder ?fg q) = 0"
      proof -
        have total' : "(\<Sum>q \<in> ?zfg. zorder ?fg q) = int (?n + 1)"
          using total hzfg by simp
        show ?thesis using sum_split inside_eq total' by linarith
      qed

      \<comment> \<open>All zeros of ?fg have finite root set (needed below).\<close>
      have fin_all: "finite {z :: complex. ?fg z = 0}"
      proof -
        have nz': "[:-1,1:] * ?cp \<noteq> (0 :: complex poly)"
          by (metis cp_nz mult_eq_0_iff pCons_eq_0_iff zero_neq_one)
        have sub: "{z. ?fg z = 0} \<subseteq> {z. poly ([:-1,1:] * ?cp) z = 0}"
          by (auto simp: poly_mult algebra_simps)
        from finite_subset[OF sub poly_roots_finite[OF nz']] show ?thesis .
      qed

      have fg_holo: "?fg holomorphic_on UNIV"
        unfolding poly_altdef by (intro holomorphic_intros)

      \<comment> \<open>Every zero of ?fg has zorder ≥ 1.\<close>
      have fg_zorder_pos: "\<forall>q \<in> ?zfg. 1 \<le> zorder ?fg q"
      proof (intro ballI)
        fix q assume hq: "q \<in> ?zfg"
        show "1 \<le> zorder ?fg q"
        proof (rule zorder_pos_at_zero)
          show "?fg q = 0" using hq hzfg by auto
          show "?fg analytic_on {q}"
            by (auto simp: analytic_on_def
                    intro!: exI[of _ 1] holomorphic_on_subset[OF fg_holo])
          show "\<exists>\<^sub>F z in nhds q. ?fg z \<noteq> 0"
          proof (rule ccontr)
            assume "\<not> (\<exists>\<^sub>F z in nhds q. ?fg z \<noteq> 0)"
            hence evq: "eventually (\<lambda>z. ?fg z = 0) (nhds q)"
              by (simp add: frequently_def)
            obtain V where hV: "open V" "q \<in> V" "\<forall>z \<in> V. ?fg z = 0"
              using eventually_nhds [THEN iffD1, OF evq] by auto
            obtain eps where heps: "0 < eps" "ball q eps \<subseteq> V"
              using open_contains_ball hV by blast
            have "infinite (ball q eps)"
              using uncountable_ball[OF heps(1)] uncountable_infinite by blast
            moreover have "ball q eps \<subseteq> {z :: complex. ?fg z = 0}"
              using heps(2) hV(3) by blast
            ultimately show False using finite_subset fin_all by blast
          qed
        qed
      qed

      have hzorder_w : "1 \<le> zorder ?fg w"
        using fg_zorder_pos hw_in by blast

      have outside_pos :
        "1 \<le> (\<Sum>q \<in> {q \<in> ?zfg. r \<le> norm q}. zorder ?fg q)"
      proof -
        have hmem: "w \<in> {q \<in> ?zfg. r \<le> norm q}"
          using hw_in hnr by simp
        have fin2: "finite {q \<in> ?zfg. r \<le> norm q}"
          by (rule finite_subset[OF _ fin_zfg]) auto
        have "zorder ?fg w \<le> (\<Sum>q \<in> {q \<in> ?zfg. r \<le> norm q}. zorder ?fg q)"
        proof (rule member_le_sum[OF hmem _ fin2])
          fix x assume "x \<in> {q \<in> ?zfg. r \<le> norm q} - {w}"
          hence "x \<in> ?zfg" by auto
          with fg_zorder_pos show "0 \<le> zorder ?fg x" by auto
        qed
        with hzorder_w show ?thesis by linarith
      qed

      show False using outside_zero outside_pos by linarith
    qed
  qed

  \<comment> \<open>Apply to z: since ?fg z = 0, for all r > 1, norm z < r, so norm z ≤ 1.\<close>
  show "norm z \<le> 1"
  proof (rule ccontr)
    assume "\<not> norm z \<le> 1"
    hence "1 < norm z" by simp
    with zeros_in_ball hfgz have "norm z < norm z"
      by blast
    thus False by simp
  qed
qed

end
