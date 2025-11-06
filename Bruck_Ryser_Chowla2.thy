(* Title: Bruck_Ryser_Chowla2
   Author: Craig Alan Feinstein
*)

theory Bruck_Ryser_Chowla2 imports
  Design_Theory.Bruck_Ryser_Chowla

context ordered_sym_bibd

begin 

lemma linear_comb_of_y_part_1:
  fixes a :: "nat"
  fixes b :: "nat"
  fixes c :: "nat"
  fixes d :: "nat"
  fixes x :: "rat mat"
  fixes x0 :: "rat"
  fixes x1 :: "rat"
  fixes x2 :: "rat"
  fixes x3 :: "rat"
  fixes i :: "nat"
  fixes m :: "nat"
  assumes "a^2 + b^2 + c^2 + d^2 = \<k> - \<Lambda>"
           "\<v> \<ge> m" "m > 3" "i \<in> {0..<4}" "x0 = x $$ (m-4,0)" 
          "x1 = x $$ (m-3,0)" "x2 = x $$ (m-2,0)" "x3 = x $$ (m-1,0)"       
  shows "\<exists>e0 e1 e2 e3 :: rat.(\<Sum>h \<in> {0..<m}. 
          of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) =   
          e0 * one_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          e1 * two_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          e2 * three_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          e3 * four_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))"
proof -
  have key: "y_inv_reversible(y_reversible((a, b, c, d),(x0, x1, x2, x3))) = 
         ((a, b, c, d),(x0, x1, x2, x3))" 
  using y_inverses_part_1 assms(1) blocksize_gt_index 
  by (metis less_numeral_extra(3) zero_less_diff)

  let ?D = "of_nat (a^2 + b^2 + c^2 + d^2) :: rat"
  let ?y0 = "one_of(y_of((a, b, c, d),(x0, x1, x2, x3)))" 
  let ?y1 = "two_of(y_of((a, b, c, d),(x0, x1, x2, x3)))"
  let ?y2 = "three_of(y_of((a, b, c, d),(x0, x1, x2, x3)))"
  let ?y3 = "four_of(y_of((a, b, c, d),(x0, x1, x2, x3)))"
  let ?e0 = "of_int(N $$ (m-4,m-i-1)) * (of_nat a)/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat b)/?D +
             of_int(N $$ (m-2,m-i-1)) * (of_nat c)/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat d)/?D"
  let ?e1 = "-of_int(N $$ (m-4,m-i-1)) * (of_nat b)/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat a)/?D -
              of_int(N $$ (m-2,m-i-1)) * (of_nat d)/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat c)/?D"
  let ?e2 = "-of_int(N $$ (m-4,m-i-1)) * (of_nat c)/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat d)/?D +
              of_int(N $$ (m-2,m-i-1)) * (of_nat a)/?D - of_int(N $$ (m-1,m-i-1)) * (of_nat b)/?D"
  let ?e3 = "-of_int(N $$ (m-4,m-i-1)) * (of_nat d)/?D - of_int(N $$ (m-3,m-i-1)) * (of_nat c)/?D +
              of_int(N $$ (m-2,m-i-1)) * (of_nat b)/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat a)/?D"

  have oneof: "x0 = 
    one_of(snd(y_inv_reversible(y_reversible((a, b, c, d),(x0, x1, x2, x3)))))"
    using key by auto
  then have "x0 = ((of_nat a)*?y0 - (of_nat b)*?y1 - (of_nat c)*?y2 - (of_nat d)*?y3)/?D"
    by simp
  then have first_1: "of_int(N $$ (m-4,m-i-1)) * x0 = of_int(N $$ (m-4,m-i-1)) *
    ((of_nat a)*?y0 - (of_nat b)*?y1 - (of_nat c)*?y2 - (of_nat d)*?y3)/?D" 
    by (metis (mono_tags, lifting) times_divide_eq_right)
  have first_2: "of_int(N $$ (m-4,m-i-1)) * ((of_nat a)*?y0 - (of_nat b)*?y1 - (of_nat c)*?y2 - 
    (of_nat d)*?y3)/?D = of_int(N $$ (m-4,m-i-1)) * (of_nat a)*?y0/?D - 
    of_int(N $$ (m-4,m-i-1)) * (of_nat b)*?y1/?D - of_int(N $$ (m-4,m-i-1)) * (of_nat c)*?y2/?D -
    of_int(N $$ (m-4,m-i-1)) * (of_nat d)*?y3/?D" 
    by (simp add: of_rat_diff of_rat_mult right_diff_distrib divide_simps)
  then have first: "of_int(N $$ (m-4,m-i-1)) * x0 = of_int(N $$ (m-4,m-i-1)) * (of_nat a)*?y0/?D - 
    of_int(N $$ (m-4,m-i-1)) * (of_nat b)*?y1/?D - of_int(N $$ (m-4,m-i-1)) * (of_nat c)*?y2/?D - 
    of_int(N $$ (m-4,m-i-1)) * (of_nat d)*?y3/?D" 
    using first_1 first_2 by argo

  have twoof: "x1 = 
    two_of(snd(y_inv_reversible(y_reversible((a, b, c, d),(x0, x1, x2, x3)))))"
    using key by auto
  then have "x1 = ((of_nat b)*?y0 + (of_nat a)*?y1 + (of_nat d)*?y2 - (of_nat c)*?y3)/?D"
    by simp
  then have second_1: "of_int(N $$ (m-3,m-i-1)) * x1 = of_int(N $$ (m-3,m-i-1)) *
    ((of_nat b)*?y0 + (of_nat a)*?y1 + (of_nat d)*?y2 - (of_nat c)*?y3)/?D" 
    by (metis (mono_tags, lifting) times_divide_eq_right)
  have second_2: "of_int(N $$ (m-3,m-i-1)) * ((of_nat b)*?y0 + (of_nat a)*?y1 + (of_nat d)*?y2 - 
    (of_nat c)*?y3)/?D = of_int(N $$ (m-3,m-i-1)) * ((of_nat b)*?y0 + (of_nat a)*?y1 + 
    (of_nat d)*?y2)/?D - of_int(N $$ (m-3,m-i-1)) * (of_nat c)*?y3/?D" 
    by (simp add: of_rat_diff of_rat_mult right_diff_distrib divide_simps)
  have second_3: "of_int(N $$ (m-3,m-i-1)) *((of_nat b)*?y0 + (of_nat a)*?y1 + 
    (of_nat d)*?y2)/?D = (of_int(N $$ (m-3,m-i-1)) * (of_nat b)*?y0 + 
    of_int(N $$ (m-3,m-i-1)) * (of_nat a)*?y1 + of_int(N $$ (m-3,m-i-1)) * (of_nat d)*?y2)/?D"
    by (simp add: of_rat_add of_rat_mult distrib_left)
  have second_4: "(of_int(N $$ (m-3,m-i-1)) * (of_nat b)*?y0 + of_int(N $$ (m-3,m-i-1)) * (of_nat a)*?y1 + 
    of_int(N $$ (m-3,m-i-1)) * (of_nat d)*?y2)/?D = of_int(N $$ (m-3,m-i-1)) * (of_nat b)*?y0/?D + 
    of_int(N $$ (m-3,m-i-1)) * (of_nat a)*?y1/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat d)*?y2/?D"
    by (simp add: of_rat_add of_rat_mult add_divide_distrib)
  then have "(of_int(N $$ (m-3,m-i-1)) * (of_nat b)*?y0 + of_int(N $$ (m-3,m-i-1)) * (of_nat a)*?y1 + 
    of_int(N $$ (m-3,m-i-1)) * (of_nat d)*?y2)/?D - of_int(N $$ (m-3,m-i-1)) * (of_nat c)*?y3/?D = 
    of_int(N $$ (m-3,m-i-1)) * (of_nat b)*?y0/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat a)*?y1/?D + 
    of_int(N $$ (m-3,m-i-1)) * (of_nat d)*?y2/?D - of_int(N $$ (m-3,m-i-1)) * (of_nat c)*?y3/?D" 
    by presburger
  then have second: "of_int(N $$ (m-3,m-i-1)) * x1 = of_int(N $$ (m-3,m-i-1)) * (of_nat b)*?y0/?D +
     of_int(N $$ (m-3,m-i-1)) * (of_nat a)*?y1/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat d)*?y2/?D - 
     of_int(N $$ (m-3,m-i-1)) * (of_nat c)*?y3/?D"
    using second_1 second_2 second_3 second_4 by argo

  have threeof: "x2 = 
    three_of(snd(y_inv_reversible(y_reversible((a, b, c, d),(x0, x1, x2, x3)))))"
    using key by auto
  then have "x2 = ((of_nat c)*?y0 + (of_nat a)*?y2 + (of_nat b)*?y3 - (of_nat d)*?y1)/?D"
    by simp
  then have third_1: "of_int(N $$ (m-2,m-i-1)) * x2 = of_int(N $$ (m-2,m-i-1)) *
    ((of_nat c)*?y0 + (of_nat a)*?y2 + (of_nat b)*?y3 - (of_nat d)*?y1)/?D" 
    by (metis (mono_tags, lifting) times_divide_eq_right) 
  have third_2: "of_int(N $$ (m-2,m-i-1)) * ((of_nat c)*?y0 + (of_nat a)*?y2 + (of_nat b)*?y3 - 
    (of_nat d)*?y1)/?D = of_int(N $$ (m-2,m-i-1)) * ((of_nat c)*?y0 + (of_nat a)*?y2 + (of_nat b)*?y3)/?D - 
    of_int(N $$ (m-2,m-i-1)) * (of_nat d)*?y1/?D" 
    by (simp add: of_rat_diff of_rat_mult right_diff_distrib divide_simps)
  have third_3: "of_int(N $$ (m-2,m-i-1)) *((of_nat c)*?y0 + (of_nat a)*?y2 + 
    (of_nat b)*?y3)/?D = (of_int(N $$ (m-2,m-i-1)) * (of_nat c)*?y0 + 
    of_int(N $$ (m-2,m-i-1)) * (of_nat a)*?y2 + of_int(N $$ (m-2,m-i-1)) * (of_nat b)*?y3)/?D"
    by (simp add: of_rat_add of_rat_mult distrib_left)
  have third_4: "(of_int(N $$ (m-2,m-i-1)) * (of_nat c)*?y0 + of_int(N $$ (m-2,m-i-1)) * (of_nat a)*?y2 + 
    of_int(N $$ (m-2,m-i-1)) * (of_nat b)*?y3)/?D = of_int(N $$ (m-2,m-i-1)) * (of_nat c)*?y0/?D + 
    of_int(N $$ (m-2,m-i-1)) * (of_nat a)*?y2/?D + of_int(N $$ (m-2,m-i-1)) * (of_nat b)*?y3/?D"
    by (simp add: of_rat_add of_rat_mult add_divide_distrib)
  then have "(of_int(N $$ (m-2,m-i-1)) * (of_nat c)*?y0 + of_int(N $$ (m-2,m-i-1)) * (of_nat a)*?y2 + 
    of_int(N $$ (m-2,m-i-1)) * (of_nat b)*?y3)/?D - of_int(N $$ (m-2,m-i-1)) * (of_nat d)*?y1/?D = 
    of_int(N $$ (m-2,m-i-1)) * (of_nat c)*?y0/?D + of_int(N $$ (m-2,m-i-1)) * (of_nat a)*?y2/?D + 
    of_int(N $$ (m-2,m-i-1)) * (of_nat b)*?y3/?D - of_int(N $$ (m-2,m-i-1)) * (of_nat d)*?y1/?D" 
    by presburger
  then have third: "of_int(N $$ (m-2,m-i-1)) * x2 = of_int(N $$ (m-2,m-i-1)) * (of_nat c)*?y0/?D +
     of_int(N $$ (m-2,m-i-1)) * (of_nat a)*?y2/?D + of_int(N $$ (m-2,m-i-1)) * (of_nat b)*?y3/?D - 
     of_int(N $$ (m-2,m-i-1)) * (of_nat d)*?y1/?D"
    using third_1 third_2 third_3 third_4 by argo

  have fourof: "x3 = 
    four_of(snd(y_inv_reversible(y_reversible((a, b, c, d),(x0, x1, x2, x3)))))"
    using key by auto
  then have "x3 = ((of_nat d)*?y0 + (of_nat c)*?y1 + (of_nat a)*?y3 - (of_nat b)*?y2)/?D"
    by simp
  then have fourth_1: "of_int(N $$ (m-1,m-i-1)) * x3 = of_int(N $$ (m-1,m-i-1)) *
    ((of_nat d)*?y0 + (of_nat c)*?y1 + (of_nat a)*?y3 - (of_nat b)*?y2)/?D" 
    by (metis (mono_tags, lifting) times_divide_eq_right) 
  have fourth_2: "of_int(N $$ (m-1,m-i-1)) * ((of_nat d)*?y0 + (of_nat c)*?y1 + (of_nat a)*?y3 - 
    (of_nat b)*?y2)/?D = of_int(N $$ (m-1,m-i-1)) * ((of_nat d)*?y0 + (of_nat c)*?y1 +
    (of_nat a)*?y3)/?D - of_int(N $$ (m-1,m-i-1)) * (of_nat b)*?y2/?D" 
    by (simp add: of_rat_diff of_rat_mult right_diff_distrib divide_simps)
  have fourth_3: "of_int(N $$ (m-1,m-i-1)) *((of_nat d)*?y0 + (of_nat c)*?y1 + 
    (of_nat a)*?y3)/?D = (of_int(N $$ (m-1,m-i-1)) * (of_nat d)*?y0 + 
    of_int(N $$ (m-1,m-i-1)) * (of_nat c)*?y1 + of_int(N $$ (m-1,m-i-1)) * (of_nat a)*?y3)/?D"
    by (simp add: of_rat_add of_rat_mult distrib_left)
  have fourth_4: "(of_int(N $$ (m-1,m-i-1)) * (of_nat d)*?y0 + of_int(N $$ (m-1,m-i-1)) * (of_nat c)*?y1 + 
    of_int(N $$ (m-1,m-i-1)) * (of_nat a)*?y3)/?D = of_int(N $$ (m-1,m-i-1)) * (of_nat d)*?y0/?D + 
    of_int(N $$ (m-1,m-i-1)) * (of_nat c)*?y1/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat a)*?y3/?D"
    by (simp add: of_rat_add of_rat_mult add_divide_distrib)
  then have "(of_int(N $$ (m-1,m-i-1)) * (of_nat d)*?y0 + of_int(N $$ (m-1,m-i-1)) * (of_nat c)*?y1 + 
    of_int(N $$ (m-1,m-i-1)) * (of_nat a)*?y3)/?D - of_int(N $$ (m-1,m-i-1)) * (of_nat b)*?y2/?D = 
    of_int(N $$ (m-1,m-i-1)) * (of_nat d)*?y0/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat c)*?y1/?D + 
    of_int(N $$ (m-1,m-i-1)) * (of_nat a)*?y3/?D - of_int(N $$ (m-1,m-i-1)) * (of_nat b)*?y2/?D" 
    by presburger
  then have fourth: "of_int(N $$ (m-1,m-i-1)) * x3 = of_int(N $$ (m-1,m-i-1)) * (of_nat d)*?y0/?D +
     of_int(N $$ (m-1,m-i-1)) * (of_nat c)*?y1/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat a)*?y3/?D - 
     of_int(N $$ (m-1,m-i-1)) * (of_nat b)*?y2/?D"
    using fourth_1 fourth_2 fourth_3 fourth_4 by argo 

  have sum: "of_int(N $$ (m-4,m-i-1)) * x0 + of_int(N $$ (m-3,m-i-1)) * x1 + 
    of_int(N $$ (m-2,m-i-1)) * x2 + of_int(N $$ (m-1,m-i-1)) * x3 =
    of_int(N $$ (m-4,m-i-1)) * (of_nat a)*?y0/?D - of_int(N $$ (m-4,m-i-1)) * (of_nat b)*?y1/?D - 
    of_int(N $$ (m-4,m-i-1)) * (of_nat c)*?y2/?D - of_int(N $$ (m-4,m-i-1)) * (of_nat d)*?y3/?D +
    of_int(N $$ (m-3,m-i-1)) * (of_nat b)*?y0/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat a)*?y1/?D +
    of_int(N $$ (m-3,m-i-1)) * (of_nat d)*?y2/?D - of_int(N $$ (m-3,m-i-1)) * (of_nat c)*?y3/?D +
    of_int(N $$ (m-2,m-i-1)) * (of_nat c)*?y0/?D - of_int(N $$ (m-2,m-i-1)) * (of_nat d)*?y1/?D + 
    of_int(N $$ (m-2,m-i-1)) * (of_nat a)*?y2/?D + of_int(N $$ (m-2,m-i-1)) * (of_nat b)*?y3/?D + 
    of_int(N $$ (m-1,m-i-1)) * (of_nat d)*?y0/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat c)*?y1/?D - 
    of_int(N $$ (m-1,m-i-1)) * (of_nat b)*?y2/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat a)*?y3/?D"
    using first second third fourth by linarith
  have sumdef: "(\<Sum>h \<in> {0..<4}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) = 
        of_int(N $$ (m-4,m-i-1)) * x $$ (m-4,0) + of_int(N $$ (m-3,m-i-1)) * x $$ (m-3,0) + 
        of_int(N $$ (m-2,m-i-1)) * x $$ (m-2,0) + of_int(N $$ (m-1,m-i-1)) * x $$ (m-1,0)" 
    by (simp add: numeral.simps(2,3))
  have split: "{0..<m} = {0..<4} \<union> {4..<m}" using assms(3) by auto
  have inter: "{} = {0..<4} \<inter> {4..<m}" by auto
  have "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) =
        (\<Sum>h \<in> {0..<4}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) + 
        (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))"
    using split inter sum.union_disjoint[of "{0..<4}" "{4..<m}" "\<lambda> h . 
    (of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))"] 
    by (metis (no_types, lifting) finite_atLeastLessThan)
  then have "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) = 
        of_int(N $$ (m-4,m-i-1)) * x0 + of_int(N $$ (m-3,m-i-1)) * x1 +
        of_int(N $$ (m-2,m-i-1)) * x2 + of_int(N $$ (m-1,m-i-1)) * x3 +
        (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))"
    using sumdef assms(4-8) by argo
  then have "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) =   
    of_int(N $$ (m-4,m-i-1)) * (of_nat a)*?y0/?D - of_int(N $$ (m-4,m-i-1)) * (of_nat b)*?y1/?D - 
    of_int(N $$ (m-4,m-i-1)) * (of_nat c)*?y2/?D - of_int(N $$ (m-4,m-i-1)) * (of_nat d)*?y3/?D +
    of_int(N $$ (m-3,m-i-1)) * (of_nat b)*?y0/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat a)*?y1/?D +
    of_int(N $$ (m-3,m-i-1)) * (of_nat d)*?y2/?D - of_int(N $$ (m-3,m-i-1)) * (of_nat c)*?y3/?D +
    of_int(N $$ (m-2,m-i-1)) * (of_nat c)*?y0/?D - of_int(N $$ (m-2,m-i-1)) * (of_nat d)*?y1/?D + 
    of_int(N $$ (m-2,m-i-1)) * (of_nat a)*?y2/?D + of_int(N $$ (m-2,m-i-1)) * (of_nat b)*?y3/?D + 
    of_int(N $$ (m-1,m-i-1)) * (of_nat d)*?y0/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat c)*?y1/?D - 
    of_int(N $$ (m-1,m-i-1)) * (of_nat b)*?y2/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat a)*?y3/?D +
    (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))" using sum by argo
  then have "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) =   
    of_int(N $$ (m-4,m-i-1)) * (of_nat a)*?y0/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat b)*?y0/?D +
    of_int(N $$ (m-2,m-i-1)) * (of_nat c)*?y0/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat d)*?y0/?D -
    of_int(N $$ (m-4,m-i-1)) * (of_nat b)*?y1/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat a)*?y1/?D -
    of_int(N $$ (m-2,m-i-1)) * (of_nat d)*?y1/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat c)*?y1/?D -
    of_int(N $$ (m-4,m-i-1)) * (of_nat c)*?y2/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat d)*?y2/?D +
    of_int(N $$ (m-2,m-i-1)) * (of_nat a)*?y2/?D - of_int(N $$ (m-1,m-i-1)) * (of_nat b)*?y2/?D -
    of_int(N $$ (m-4,m-i-1)) * (of_nat d)*?y3/?D - of_int(N $$ (m-3,m-i-1)) * (of_nat c)*?y3/?D +
    of_int(N $$ (m-2,m-i-1)) * (of_nat b)*?y3/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat a)*?y3/?D +
    (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))" by (simp add: algebra_simps)
  then have "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) = 
    (of_int(N $$ (m-4,m-i-1)) * (of_nat a)/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat b)/?D +
     of_int(N $$ (m-2,m-i-1)) * (of_nat c)/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat d)/?D) * ?y0 +
    (-of_int(N $$ (m-4,m-i-1)) * (of_nat b)/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat a)/?D -
     of_int(N $$ (m-2,m-i-1)) * (of_nat d)/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat c)/?D) * ?y1 +
    (-of_int(N $$ (m-4,m-i-1)) * (of_nat c)/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat d)/?D +
     of_int(N $$ (m-2,m-i-1)) * (of_nat a)/?D - of_int(N $$ (m-1,m-i-1)) * (of_nat b)/?D) * ?y2 +
    (-of_int(N $$ (m-4,m-i-1)) * (of_nat d)/?D - of_int(N $$ (m-3,m-i-1)) * (of_nat c)/?D +
     of_int(N $$ (m-2,m-i-1)) * (of_nat b)/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat a)/?D) * ?y3 +
    (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))" by (simp add: algebra_simps)
  then have "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) = 
    ?e00 * ?y0 + ?e01 * ?y1 + ?e02 * ?y2 + ?e03 * ?y3 +
    (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))" by blast
  then show ?thesis by blast
qed

lemma linear_comb_of_y_part_2:
  fixes a :: "nat"
  fixes b :: "nat"
  fixes c :: "nat"
  fixes d :: "nat"
  fixes y0 :: "rat"
  fixes y1 :: "rat"
  fixes y2 :: "rat"
  fixes y3 :: "rat"
  fixes x :: "rat mat"
  fixes x0 :: "rat"
  fixes x1 :: "rat"
  fixes x2 :: "rat"
  fixes x3 :: "rat"
  fixes i :: "nat"
  fixes m :: "nat"
  assumes "a^2 + b^2 + c^2 + d^2 = (\<k> - \<Lambda>)"
          "\<v> \<ge> m" "m > 3" "i \<in> {0..<4}" "x0 = x $$ (m-4,0)" 
          "x1 = x $$ (m-3,0)" "x2 = x $$ (m-2,0)" "x3 = x $$ (m-1,0)"   
          "x0 = one_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
          "x1 = two_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
          "x2 = three_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
          "x3 = four_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
  shows "\<exists>e0 e1 e2 e3 :: rat.(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) = 
    e0 * y0 + e1 * y1 + e2 * y2 + e3 * y3 +
    (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))"
proof -
  
  have "\<exists>e0 e1 e2 e3 :: rat.(\<Sum>h \<in> {0..<m}. 
          of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) =   
          e0 * one_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          e1 * two_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          e2 * three_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          e3 * four_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))"
     using linear_comb_of_y_part_1 assms(1-12) by simp
  then have "\<exists>e0 e1 e2 e3 :: rat.(\<Sum>h \<in> {0..<m}. 
          of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) =   
          e0 * one_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          e1 * two_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          e2 * three_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          e3 * four_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))"
    by simp

   then obtain e0 e1 e2 e3 where eq1:
    "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) = 
    e0 * one_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
    e1 * two_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
    e2 * three_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
    e3 * four_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
    (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))"
     by fast

  have "((a, b, c, d),(x0, x1, x2, x3)) = 
        y_inv_reversible((a, b, c, d),(y0, y1, y2, y3))"
    using assms(9-12) by simp
  then have "y_reversible((a, b, c, d),(x0, x1, x2, x3)) = 
        y_reversible(y_inv_reversible((a, b, c, d),(y0, y1, y2, y3)))"
    by simp
  then have eq2: "y_reversible((a, b, c, d),(x0, x1, x2, x3)) =
    ((a, b, c, d),(y0, y1, y2, y3))" 
    using y_inverses_part_2 assms(1) assms(9-12) blocksize_gt_index 
    by (metis less_numeral_extra(3) zero_less_diff) 
  have eq3: "y0 = one_of(y_of((a, b, c, d),(x0, x1, x2, x3)))" 
    using eq2 by simp
  have eq4: "y1 = two_of(y_of((a, b, c, d),(x0, x1, x2, x3)))" 
    using eq2 by simp
  have eq5: "y2 = three_of(y_of((a, b, c, d),(x0, x1, x2, x3)))" 
    using eq2 by simp
  have eq6: "y3 = four_of(y_of((a, b, c, d),(x0, x1, x2, x3)))" 
    using eq2 by simp
  have "e0 * y0 + e1 * y1 + e2 * y2 + e3 * y3 = 
    e0 * one_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
    e1 * two_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
    e2 * three_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
    e3 * four_of(y_of((a, b, c, d),(x0, x1, x2, x3)))"
    using eq3 eq4 eq5 eq6 by simp
  thus ?thesis using eq1 by (metis (no_types, lifting))
qed

lemma lagrange_identity_x:
  fixes a :: "nat"
  fixes b :: "nat"
  fixes c :: "nat"
  fixes d :: "nat"
  fixes x0 :: "rat"
  fixes x1 :: "rat"
  fixes x2 :: "rat"
  fixes x3 :: "rat"
  fixes x :: "rat mat"
  fixes i :: "nat"
  fixes m :: "nat"
  assumes "a^2 + b^2 + c^2 + d^2 = \<k> - \<Lambda>"
          "\<v> \<ge> m" "m > 3" "i \<in> {0..<4}" "x0 = x $$ (m-4,0)" 
          "x1 = x $$ (m-3,0)" "x2 = x $$ (m-2,0)" "x3 = x $$ (m-1,0)"
  shows "of_int(\<k> - \<Lambda>) * (\<Sum>j \<in> {0..<m}. (x $$ (m-j-1, 0))^2) = 
         of_int(\<k> - \<Lambda>) * (\<Sum>j \<in> {4..<m}. (x $$ (m-j-1, 0))^2) +
         (one_of(y_of((a, b, c, d),(x0, x1, x2, x3)))^2 +
          two_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
          three_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
          four_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2)"
proof -
  have eq0: "x0^2 = (x $$ (m-4,0))^2"
    using assms(5) by (simp add: of_rat_power)
  have eq1: "x1^2 = (x $$ (m-3,0))^2"
    using assms(6) by (simp add: of_rat_power)
  have eq2: "x2^2 = (x $$ (m-2,0))^2"
    using assms(7) by (simp add: of_rat_power)
  have eq3: "x3^2 = (x $$ (m-1,0))^2"
    using assms(8) by (simp add: of_rat_power)
  have eq: "x0^2 + x1^2 + x2^2 + x3^2 = 
    (x $$ (m-4,0))^2 + (x $$ (m-3,0))^2 + (x $$ (m-2,0))^2 + (x $$ (m-1,0))^2"
    using eq0 eq1 eq2 eq3 by (simp add: of_rat_add)
  have "one_of(y_of((a, b, c, d),(x0, x1, x2, x3)))^2 +
          two_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
          three_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
          four_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 = 
          of_nat (a^2 + b^2 + c^2 + d^2) * (x0^2 + x1^2 + x2^2 + x3^2)" 
    using lagrange_trans_of_4_identity[of a b c d x0 x1 x2 x3] assms(1-8) by blast
  then have "one_of(y_of((a, b, c, d),(x0, x1, x2, x3)))^2 +
          two_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
          three_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
          four_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 = 
          of_nat (\<k> - \<Lambda>) * (x0^2 + x1^2 + x2^2 + x3^2)" using assms(1)
    by presburger
  then have keyform: "one_of(y_of((a, b, c, d),(x0, x1, x2, x3)))^2 +
          two_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
          three_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
          four_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 = 
          of_int(\<k> - \<Lambda>) * ((x $$ (m-1,0))^2 + (x $$ (m-2,0))^2 +
          (x $$ (m-3,0))^2 + (x $$ (m-4,0))^2)" using eq by simp
  have sumdef: "(\<Sum>j \<in> {0..<4}. (x $$ (m-j-1, 0))^2) = (x $$ (m-1,0))^2 + 
        (x $$ (m-2,0))^2 + (x $$ (m-3,0))^2 + (x $$ (m-4,0))^2" by (simp add: numeral.simps(2,3))
  have split: "{0..<m} = {0..<4} \<union> {4..<m}" using assms(3) by auto
  have inter: "{} = {0..<4} \<inter> {4..<m}" by auto
  have "(\<Sum>j \<in> {0..<m}. (x $$ (m-j-1, 0))^2) =
        (\<Sum>j \<in> {0..<4}. (x $$ (m-j-1, 0))^2) + 
        (\<Sum>j \<in> {4..<m}. (x $$ (m-j-1, 0))^2)"
    using split inter sum.union_disjoint[of "{0..<4}" "{4..<m}" "\<lambda> j . (x $$ (m-j-1, 0))^2"] 
    by (metis (no_types, lifting) finite_atLeastLessThan)
  then have "of_int (\<k> - \<Lambda>) * (\<Sum>j \<in> {0..<m}. (x $$ (m-j-1, 0))^2) =
        of_int (\<k> - \<Lambda>) * (\<Sum>j \<in> {0..<4}. (x $$ (m-j-1, 0))^2) + 
        of_int (\<k> - \<Lambda>) * (\<Sum>j \<in> {4..<m}. (x $$ (m-j-1, 0))^2)" using algebra_simps by simp
  then have "of_int (\<k> - \<Lambda>) * (\<Sum>j \<in> {0..<m}. (x $$ (m-j-1, 0))^2) =
        of_int (\<k> - \<Lambda>) * (\<Sum>j \<in> {4..<m}. (x $$ (m-j-1, 0))^2) +
        of_int (\<k> - \<Lambda>) * ((x $$ (m-1,0))^2 + (x $$ (m-2,0))^2 + (x $$ (m-3,0))^2 + (x $$ (m-4,0))^2)"
    using sumdef algebra_simps by auto
  then have "of_nat(\<k> - \<Lambda>) * (\<Sum>j \<in> {0..<m}. (x $$ (m-j-1, 0))^2) = 
             of_nat(\<k> - \<Lambda>) * (\<Sum>j \<in> {4..<m}. (x $$ (m-j-1, 0))^2) +
            (one_of(y_of((a, b, c, d),(x0, x1, x2, x3)))^2 +
             two_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
             three_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
             four_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2)"
    using keyform algebra_simps by auto
  thus ?thesis by simp
qed

lemma lagrange_identity_y:
  fixes a :: "nat"
  fixes b :: "nat"
  fixes c :: "nat"
  fixes d :: "nat"
  fixes x0 :: "rat"
  fixes x1 :: "rat"
  fixes x2 :: "rat"
  fixes x3 :: "rat"
  fixes y0 :: "rat"
  fixes y1 :: "rat"
  fixes y2 :: "rat"
  fixes y3 :: "rat"
  fixes x :: "rat mat"
  fixes i :: "nat"
  fixes m :: "nat"
  assumes "a^2 + b^2 + c^2 + d^2 = \<k> - \<Lambda>"
          "\<v> \<ge> m" "m > 3" "i \<in> {0..<4}" "x0 = x $$ (m-4,0)" 
          "x1 = x $$ (m-3,0)" "x2 = x $$ (m-2,0)" "x3 = x $$ (m-1,0)"
          "x0 = one_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
          "x1 = two_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
          "x2 = three_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
          "x3 = four_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
  shows   "of_int (\<k> - \<Lambda>) * (\<Sum>j \<in> {0..<m}. (x $$ (m-j-1, 0))^2) = 
           of_int (\<k> - \<Lambda>) * (\<Sum>j \<in> {4..<m}. (x $$ (m-j-1, 0))^2) +
           y0^2 + y1^2 + y2^2 + y3^2"
proof -
  have eq1: "of_int (\<k> - \<Lambda>) * (\<Sum>j \<in> {0..<m}. (x $$ (m-j-1, 0))^2) = 
             of_int (\<k> - \<Lambda>) * (\<Sum>j \<in> {4..<m}. (x $$ (m-j-1, 0))^2) +
             (one_of(y_of((a, b, c, d),(x0, x1, x2, x3)))^2 +
              two_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
              three_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
              four_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2)"
    using assms lagrange_identity_x by metis
  have "((a, b, c, d),(x0, x1, x2, x3)) = 
        y_inv_reversible((a, b, c, d),(y0, y1, y2, y3))"
    using assms by simp
  then have "y_reversible((a, b, c, d),(x0, x1, x2, x3)) = 
        y_reversible(y_inv_reversible((a, b, c, d),(y0, y1, y2, y3)))"
    by simp
  then have eq2: "y_reversible((a, b, c, d),(x0, x1, x2, x3)) =
    ((a, b, c, d),(y0, y1, y2, y3))" 
        using y_inverses_part_2 assms blocksize_gt_index 
        by (metis (no_types, lifting) neq0_conv zero_less_diff)
  have eq3: "y0^2 = one_of(y_of((a, b, c, d),(x0, x1, x2, x3)))^2" 
    using eq2 by simp
  have eq4: "y1^2 = two_of(y_of((a, b, c, d),(x0, x1, x2, x3)))^2" 
    using eq2 by simp
  have eq5: "y2^2 = three_of(y_of((a, b, c, d),(x0, x1, x2, x3)))^2" 
    using eq2 by simp
  have eq6: "y3^2 = four_of(y_of((a, b, c, d),(x0, x1, x2, x3)))^2" 
    using eq2 by simp
  have "y0^2 + y1^2 + y2^2 + y3^2 = 
        one_of(y_of((a, b, c, d),(x0, x1, x2, x3)))^2 +
        two_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
        three_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
        four_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2"
    using eq3 eq4 eq5 eq6 by simp
  thus ?thesis using eq1 by simp
qed

lemma induction_step_0:
  fixes a :: "nat"
  fixes b :: "nat"
  fixes c :: "nat"
  fixes d :: "nat"
  fixes x0 :: "rat"
  fixes x1 :: "rat"
  fixes x2 :: "rat"
  fixes x3 :: "rat"
  fixes y0 :: "rat"
  fixes y1 :: "rat"
  fixes y2 :: "rat"
  fixes y3 :: "rat"
  fixes x :: "rat mat"
  fixes m :: "nat"
  assumes "of_nat(a^2 + b^2 + c^2 + d^2) = of_int(\<k> - \<Lambda>)" "\<v> \<ge> m" "m > 3"        
        "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) = 
         e00 * y0 + e10 * y1 + e20 * y2 + e30 * y3 +
         (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))"
        "y0 = (if e00 = 1 then -(e10 * y1 + e20 * y2 + e30 * y3 +
        (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
        (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-4)) * x $$ (h,0)))/2 else  
        (e10 * y1 + e20 * y2 + e30 * y3 +
        (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
        (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-4)) * x $$ (h,0)))/(1-e00))"
  shows "y0^2 = ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-4)) * x $$ (h,0)))^2"
proof -
  have "y0^2 = ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
               (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-4)) * x $$ (h,0)))^2"
   proof (cases "e00 = 1")
     case True   
    then have "y0 = -(e10 * y1 + e20 * y2 + e30 * y3 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-4)) * x $$ (h,0)))/2"
      using assms(5) by auto
    then have eq: "-y0 = e00 * y0 + e10 * y1 + e20 * y2 + e30 * y3 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-4)) * x $$ (h,0))"
      using True by (simp add: algebra_simps)
    have "e00 * y0 + e10 * y1 + e20 * y2 + e30 * y3 +
          (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))  = 
          (\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))"
      using assms(4) by simp
    then have "-y0 = (\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
              (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-4)) * x $$ (h,0))"
      using eq by simp
    then have "(-y0)^2 = ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
              (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-4)) * x $$ (h,0)))^2"
      by argo
    then show ?thesis
      by simp
   next
    case False
    then have "y0 = (e10 * y1 + e20 * y2 + e30 * y3 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-4)) * x $$ (h,0))) / (1 - e00)"
      using assms(5) by auto
    then have "(1 - e00) * y0 = e10 * y1 + e20 * y2 + e30 * y3 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-4)) * x $$ (h,0))"
      using False by auto
    then have eq2: "y0 = e00 * y0 + e10 * y1 + e20 * y2 + e30 * y3 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-4)) * x $$ (h,0))"
      by (simp add: algebra_simps)
    then have "y0 = (\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
              (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-4)) * x $$ (h,0))"
      using assms(4) by simp     
    then have "y0^2 = ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
              (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-4)) * x $$ (h,0)))^2"
      by simp
    then show ?thesis
      by (simp add: algebra_simps)
  qed
  thus ?thesis by simp
qed

lemma induction_step_1:
  fixes a :: "nat"
  fixes b :: "nat"
  fixes c :: "nat"
  fixes d :: "nat"
  fixes x0 :: "rat"
  fixes x1 :: "rat"
  fixes x2 :: "rat"
  fixes x3 :: "rat"
  fixes y0 :: "rat"
  fixes y1 :: "rat"
  fixes y2 :: "rat"
  fixes y3 :: "rat"
  fixes x :: "rat mat"
  fixes m :: "nat"
  assumes "of_nat(a^2 + b^2 + c^2 + d^2) = of_int(\<k> - \<Lambda>)" "\<v> \<ge> m" "m > 3"
          "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) = 
            e01 * y0 + e11 * y1 + e21 * y2 + e31 * y3 +
           (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))"
           "y1 = (if e11 = 1 then -(e01 * y0 + e21 * y2 + e31 * y3 +
           (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
           (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-3)) * x $$ (h,0)))/2 else  
           (e01 * y0 + e21 * y2 + e31 * y3 +
           (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
           (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-3)) * x $$ (h,0)))/(1-e11))"
  shows "y1^2 = ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
           (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-3)) * x $$ (h,0)))^2"
proof -
  have "y1^2 = ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
              (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-3)) * x $$ (h,0)))^2"
   proof (cases "e11 = 1")
     case True   
    then have "y1 = -(e01 * y0 + e21 * y2 + e31 * y3 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-3)) * x $$ (h,0)))/2"
      using assms(5) by auto
    then have eq: "-y1 = e01 * y0 + e11 * y1 + e21 * y2 + e31 * y3 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-3)) * x $$ (h,0))"
      using True by (simp add: algebra_simps)
    have "e01 * y0 + e11 * y1 + e21 * y2 + e31 * y3 +
          (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))  = 
          (\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))"
      using assms(4) by simp
    then have "-y1 = (\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
              (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-3)) * x $$ (h,0))"
      using eq by simp
    then have "(-y1)^2 = ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
              (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-3)) * x $$ (h,0)))^2"
      by argo
    then show ?thesis
      by auto
   next
    case False
    then have "y1 = (e01 * y0 + e21 * y2 + e31 * y3 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-3)) * x $$ (h,0))) / (1 - e11)"
      using assms(5) by auto
    then have "(1 - e11) * y1 = e01 * y0 + e21 * y2 + e31 * y3 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-3)) * x $$ (h,0))"
      using False by auto
    then have eq2: "y1 = e01 * y0 + e11 * y1 + e21 * y2 + e31 * y3 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-3)) * x $$ (h,0))"
      by (simp add: algebra_simps)
    then have "y1 = (\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
              (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-3)) * x $$ (h,0))"
      using assms(4) by simp     
    then have "y1^2 = ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
              (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-3)) * x $$ (h,0)))^2"
      by simp
    then show ?thesis
      by (simp add: algebra_simps)
  qed
  thus ?thesis by simp
qed

lemma induction_step_2:
  fixes a :: "nat"
  fixes b :: "nat"
  fixes c :: "nat"
  fixes d :: "nat"
  fixes x0 :: "rat"
  fixes x1 :: "rat"
  fixes x2 :: "rat"
  fixes x3 :: "rat"
  fixes y0 :: "rat"
  fixes y1 :: "rat"
  fixes y2 :: "rat"
  fixes y3 :: "rat"
  fixes x :: "rat mat"
  fixes m :: "nat"
  assumes "of_nat(a^2 + b^2 + c^2 + d^2) = of_int(\<k> - \<Lambda>)" "\<v> \<ge> m" "m > 3"
          "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) = 
           e02 * y0 + e12 * y1 + e22 * y2 + e32 * y3 +
           (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0))"
          "y2 = (if e22 = 1 then -(e02 * y0 + e12 * y1 + e32 * y3 +
           (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
           (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-2)) * x $$ (h,0)))/2 else  
           (e02 * y0 + e12 * y1 + e32 * y3 +
           (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
           (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-2)) * x $$ (h,0)))/(1-e22))" 
  shows "y2^2 = ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
           (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-2)) * x $$ (h,0)))^2"
proof -
  have "y2^2 = ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
               (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-2)) * x $$ (h,0)))^2"
   proof (cases "e22 = 1")
     case True   
    then have "y2 = -(e02 * y0 + e12 * y1 + e32 * y3 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-2)) * x $$ (h,0)))/2"
      using assms(5) by auto
    then have eq: "-y2 = e02 * y0 + e12 * y1 + e22 * y2 + e32 * y3 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-2)) * x $$ (h,0))"
      using True by (simp add: algebra_simps)
    have "e02 * y0 + e12 * y1 + e22 * y2 + e32 * y3 +
          (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0))  = 
          (\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0))"
      using assms(4) by simp
    then have "-y2 = (\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
              (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-2)) * x $$ (h,0))"
      using eq by simp
    then have "(-y2)^2 = ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
              (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-2)) * x $$ (h,0)))^2"
      by argo
    then show ?thesis
      by simp
   next
    case False
    then have "y2 = (e02 * y0 + e12 * y1 + e32 * y3 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-2)) * x $$ (h,0))) / (1 - e22)"
      using assms(5) by auto
    then have "(1 - e22) * y2 = e02 * y0 + e12 * y1 + e32 * y3 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-2)) * x $$ (h,0))"
      using False by auto
    then have eq2: "y2 = e02 * y0 + e12 * y1 + e22 * y2 + e32 * y3 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-2)) * x $$ (h,0))"
      by (simp add: algebra_simps)
    then have "y2 = (\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
              (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-2)) * x $$ (h,0))"
      using assms(4) by simp     
    then have "y2^2 = ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
              (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-2)) * x $$ (h,0)))^2"
      by simp
    then show ?thesis
      by (simp add: algebra_simps)
  qed
  thus ?thesis by simp
qed

lemma induction_step_3:
  fixes a :: "nat"
  fixes b :: "nat"
  fixes c :: "nat"
  fixes d :: "nat"
  fixes x0 :: "rat"
  fixes x1 :: "rat"
  fixes x2 :: "rat"
  fixes x3 :: "rat"
  fixes y0 :: "rat"
  fixes y1 :: "rat"
  fixes y2 :: "rat"
  fixes y3 :: "rat"
  fixes x :: "rat mat"
  fixes m :: "nat"
  assumes "of_nat(a^2 + b^2 + c^2 + d^2) = of_int(\<k> - \<Lambda>)" "\<v> \<ge> m" "m > 3"
          "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) = 
           e03 * y0 + e13 * y1 + e23 * y2 + e33 * y3 +
           (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))"
          "y3 = (if e33 = 1 then -(e03 * y0 + e13 * y1 + e23 * y2 +
           (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
           (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-1)) * x $$ (h,0)))/2 else  
           (e03 * y0 + e13 * y1 + e23 * y2 +
           (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
           (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-1)) * x $$ (h,0)))/(1-e33))"
  shows "y3^2 = ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
           (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-1)) * x $$ (h,0)))^2"
proof -
  have first_fact: "y3^2 = ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
              (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-1)) * x $$ (h,0)))^2"
   proof (cases "e33 = 1")
     case True   
    then have "y3 = -(e03 * y0 + e13 * y1 + e23 * y2 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-1)) * x $$ (h,0)))/2"
      using assms(5) by auto
    then have eq: "-y3 = e03 * y0 + e13 * y1 + e23 * y2 + e33 * y3 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-1)) * x $$ (h,0))"
      using True by (simp add: algebra_simps)
    have "e03 * y0 + e13 * y1 + e23 * y2 + e33 * y3 +
          (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))  = 
          (\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))"
      using assms(4) by simp
    then have "-y3 = (\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
              (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-1)) * x $$ (h,0))"
      using eq by simp
    then have "(-y3)^2 = ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
              (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-1)) * x $$ (h,0)))^2"
      by argo
    then show ?thesis
      by simp
   next
    case False
    then have "y3 = (e03 * y0 + e13 * y1 + e23 * y2 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-1)) * x $$ (h,0))) / (1 - e33)"
      using assms(5) by auto
    then have "(1 - e33) * y3 = e03 * y0 + e13 * y1 + e23 * y2 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-1)) * x $$ (h,0))"
      using False by auto
    then have eq2: "y3 = e03 * y0 + e13 * y1 + e23 * y2 + e33 * y3 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-1)) * x $$ (h,0))"
      by (simp add: algebra_simps)
    then have "y3 = (\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
              (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-1)) * x $$ (h,0))"
      using assms(4) by simp     
    then have "y3^2 = ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
              (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-1)) * x $$ (h,0)))^2"
      by simp
    then show ?thesis
      by (simp add: algebra_simps)
  qed
  thus ?thesis by simp
qed

lemma brc_v_1_mod_4:
      assumes "\<v> mod 4 = 1"
        shows "\<exists>x :: rat mat.(\<Sum>j \<in> {4..<5}.
               ((\<Sum>h \<in> {0..<5}. of_int(N $$ (4-h,4-j)) * x $$ (4-h,0)) +
               (\<Sum>h \<in> {5..<\<v>}. of_int(N $$ (h,4-j)) * x $$ (h,0)))^2) =
                of_nat \<Lambda> * (\<Sum>j \<in> {0..<\<v>}.(x $$ (j, 0)))^2 +
                of_nat (\<k> - \<Lambda>) * (\<Sum>j \<in> {4..<5}. (x $$ (4-j, 0))^2)"
proof -
  obtain a b c d where lag_eq:
    "a^2 + b^2 + c^2 + d^2 = \<k> - \<Lambda>"
    using blocksize_gt_index sum_of_four_squares by metis

  fix h :: "nat"
  fix i :: "nat"
  fix j :: "nat"
  obtain m where ineq: "\<v> \<ge> m" "m > 3"
    using assms t_design_min_v by force
  define n where "n = (\<v>-m) div 4"
  fix y0 :: "rat"
  fix y1 :: "rat"
  fix y2 :: "rat"
  fix y3 :: "rat"
  define x0 where "x0 = one_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
  define x1 where "x1 = two_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
  define x2 where "x2 = three_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
  define x3 where "x3 = four_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
  define x :: "rat mat" where  "x = mat m 1 (\<lambda>(i, j).
     if j = 0 then
       if i = m - 4 then x0
       else if i = m - 3 then x1
       else if i = m - 2 then x2
       else if i = m - 1 then x3
       else 0
     else 0)"

    have "\<exists>e00 e10 e20 e30 :: rat.(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) =
          e00 * y0 + e10 * y1 + e20 * y2 + e30 * y3 +
          (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))"
      using linear_comb_of_y_part_2[where i=3] ineq lag_eq by auto
    then obtain e00 e10 e20 e30 where eq3:
         "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) = 
          e00 * y0 + e10 * y1 + e20 * y2 + e30 * y3 +
          (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))"
      by fast
    have "\<exists>e01 e11 e21 e31 :: rat.(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) = 
                 e01 * y0 + e11 * y1 + e21 * y2 + e31 * y3 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))"
      using linear_comb_of_y_part_2[where i=2] ineq lag_eq by auto
    then obtain e01 e11 e21 e31 where eq2:
         "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) = 
          e01 * y0 + e11 * y1 + e21 * y2 + e31 * y3 +
          (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))"
      by fast
    have "\<exists>e02 e12 e22 e32 :: rat.(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) = 
                 e02 * y0 + e12 * y1 + e22 * y2 + e32 * y3 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0))"
      using linear_comb_of_y_part_2[where i=1] ineq lag_eq by auto
    then obtain e02 e12 e22 e32 where eq1:
         "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) = 
          e02 * y0 + e12 * y1 + e22 * y2 + e32 * y3 +
          (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0))"
      by fast
    have "\<exists>e03 e13 e23 e33 :: rat.(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) = 
                 e03 * y0 + e13 * y1 + e23 * y2 + e33 * y3 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))"
      using linear_comb_of_y_part_2[where i=0] ineq lag_eq by auto
    then obtain e03 e13 e23 e33 where eq0:
         "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) = 
          e03 * y0 + e13 * y1 + e23 * y2 + e33 * y3 +
          (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))"
     by fast

  define y0 where "y0 = (if e00 = 1 then -(e10 * y1 + e20 * y2 + e30 * y3 +
                  (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
                  (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-4)) * x $$ (h,0)))/2 else  
                  (e10 * y1 + e20 * y2 + e30 * y3 +
                  (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
                  (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-4)) * x $$ (h,0)))/(1-e00))"
  define y1 where "y1 = (if e11 = 1 then -(e01 * y0 + e21 * y2 + e31 * y3 +
                  (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
                  (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-3)) * x $$ (h,0)))/2 else  
                  (e01 * y0 + e21 * y2 + e31 * y3 +
                  (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
                  (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-3)) * x $$ (h,0)))/(1-e11))"
  define y2 where "y2 = (if e22 = 1 then -(e02 * y0 + e12 * y1 + e32 * y3 +
                  (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
                  (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-2)) * x $$ (h,0)))/2 else  
                  (e02 * y0 + e12 * y1 + e32 * y3 +
                  (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
                  (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-2)) * x $$ (h,0)))/(1-e22))"
  define y3 where "y3 = (if e33 = 1 then -(e03 * y0 + e13 * y1 + e23 * y2 +
                  (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
                  (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-1)) * x $$ (h,0)))/2 else  
                  (e03 * y0 + e13 * y1 + e23 * y2 +
                  (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
                  (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-1)) * x $$ (h,0)))/(1-e33))"

  let ?L0 = "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
             (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-4)) * x $$ (h,0))"
  let ?L1 = "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
             (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-3)) * x $$ (h,0))"
  let ?L2 = "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
             (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-2)) * x $$ (h,0))"
  let ?L3 = "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
             (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-1)) * x $$ (h,0))"
   
   have sumdef: "(\<Sum>j \<in> {0..<4}.((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-j-1)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-j-1)) * x $$ (h,0)))^2) = 
                  ?L0^2 + ?L1^2 + ?L2^2 + ?L3^2"
     by (simp add: numeral.simps(2,3))
   have split1: "{0..<m} = {0..<4} \<union> {4..<m}" using ineq by auto
   have inter1: "{} = {0..<4} \<inter> {4..<m}" by auto
   have trick1: "(\<Sum>j \<in> {0..<m}. ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-j-1)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-j-1)) * x $$ (h,0)))^2) =
        (\<Sum>j \<in> {0..<4}. ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-j-1)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-j-1)) * x $$ (h,0)))^2) + 
        (\<Sum>j \<in> {4..<m}. ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-j-1)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-j-1)) * x $$ (h,0)))^2)"
     using split1 inter1 sum.union_disjoint[of "{0..<4}" "{4..<m}" "\<lambda> j . 
      ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-j-1)) * x $$ (m-h-1,0)) +
      (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-j-1)) * x $$ (h,0)))^2"] 
     by (metis (no_types, lifting) finite_atLeastLessThan)
   then have lhs: "(\<Sum>j \<in> {0..<m}.((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-j-1)) * x $$ (m-h-1,0)) +
                  (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-j-1)) * x $$ (h,0)))^2) =
                  ?L0^2 + ?L1^2 + ?L2^2 + ?L3^2 + 
                  (\<Sum>j \<in> {4..<m}. ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-j-1)) * x $$ (m-h-1,0)) +
                  (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-j-1)) * x $$ (h,0)))^2)"
    using sumdef by algebra

    have "(\<Sum>h \<in> {0..<\<v>}. N $$ (h,i) * x $$ (h,0)) = 
        (\<Sum>h \<in> {0..<\<v>}. N $$ (\<v>-h-1,i) * x $$ (\<v>-h-1,0))"
      by (rule sum.reindex_bij_witness[of _ "\<lambda>h. \<v>-h-1" "\<lambda>h. \<v>-h-1"]) auto
    then have first: "(\<Sum>i \<in> {0..<\<v>}. (\<Sum>h \<in> {0..<\<v>}. N $$ (h,i) * x $$ (h,0))) = 
        (\<Sum>i \<in> {0..<\<v>}.(\<Sum>h \<in> {0..<\<v>}. N $$ (\<v>-h-1,i) * x $$ (\<v>-h-1,0)))"
      by simp
    have "(\<Sum>i \<in> {0..<\<v>}. N $$ (\<v>-h-1,i) * x $$ (\<v>-h-1,0)) =
        (\<Sum>i \<in> {0..<\<v>}. N $$ (\<v>-h-1,\<v>-i-1) * x $$ (\<v>-h-1,0))"
      by (rule sum.reindex_bij_witness[of _ "\<lambda>i. \<v>-i-1" "\<lambda>i. \<v>-i-1"]) auto
    have "(\<Sum>i \<in> {0..<\<v>}.(\<Sum>h \<in> {0..<\<v>}. N $$ (h,i) * x $$ (h,0))) = 
        (\<Sum>i \<in> {0..<\<v>}.(\<Sum>h \<in> {0..<\<v>}. N $$ (\<v>-h-1,i) * x $$ (\<v>-h-1,0)))"
      using first by auto

    have "(\<Sum>i \<in> {0..<\<v>}.(\<Sum>h \<in> {0..<\<v>}. N $$ (h,i) * x $$ (h,0))^2) =
                of_int \<Lambda> * (\<Sum>j \<in> {0..<\<v>}.(x $$ (j, 0)))^2 +
                of_int (\<k> - \<Lambda>) * (\<Sum>j \<in> {0..<\<v>}. (x $$ (j, 0))^2)"
      using brc_x_equation by auto
    then have base: "(\<Sum>i \<in> {0..<\<v>}.(\<Sum>h \<in> {0..<\<v>}. N $$ (h,\<v>-i+1) * x $$ (h,0))^2) =
                of_int \<Lambda> * (\<Sum>j \<in> {0..<\<v>}.(x $$ (j, 0)))^2 +
                of_int (\<k> - \<Lambda>) * (\<Sum>j \<in> {0..<\<v>}. (x $$ (j, 0))^2)"
      by auto
    have split2: "{0..<\<v>} = {0..<4} \<union> {4..<\<v>}" using ineq by auto
    have inter2: "{} = {0..<4} \<inter> {4..<\<v>}" by auto
    have trick2: "(\<Sum>j \<in> {0..<\<v>}.(\<Sum>h \<in> {0..<\<v>}. of_int(N $$ (\<v>-h-1,\<v>-j-1)) * x $$ (\<v>-h-1,0))^2) =
          (\<Sum>j \<in> {0..<4}.(\<Sum>h \<in> {0..<\<v>}. of_int(N $$ (\<v>-h-1,\<v>-j-1)) * x $$ (\<v>-h-1,0))^2) +
          (\<Sum>j \<in> {4..<\<v>}.(\<Sum>h \<in> {0..<\<v>}. of_int(N $$ (\<v>-h-1,\<v>-j-1)) * x $$ (\<v>-h-1,0))^2)"
      using split2 inter2 sum.union_disjoint[of "{0..<4}" "{4..<\<v>}" "\<lambda> j . 
      ((\<Sum>h \<in> {0..<\<v>}. of_int(N $$ (\<v>-h-1,\<v>-j-1)) * x $$ (\<v>-h-1,0)))^2"]
      by (metis (no_types, lifting) finite_atLeastLessThan)
    have "(\<Sum>j \<in> {0..<\<v>}. (x $$ (j, 0))^2) =
          (\<Sum>j \<in> {0..<4}. (x $$ (j, 0))^2) +
          (\<Sum>j \<in> {4..<\<v>}. (x $$ (j, 0))^2)"
      using split2 inter2 sum.union_disjoint[of "{0..<4}" "{4..<\<v>}" "\<lambda> j. (x $$ (j, 0))^2"]
      by auto
    then have trick3: "of_int (\<k> - \<Lambda>) * (\<Sum>j \<in> {0..<\<v>}. (x $$ (j, 0))^2) =
                  of_int (\<k> - \<Lambda>) * (\<Sum>j \<in> {0..<4}. (x $$ (j, 0))^2) +
                  of_int (\<k> - \<Lambda>) * (\<Sum>j \<in> {4..<\<v>}. (x $$ (j, 0))^2)"
      by (simp add: algebra_simps)
    have "(\<Sum>j \<in> {0..<\<v>}.(\<Sum>h \<in> {0..<\<v>}. of_int(N $$ (\<v>-h-1,\<v>-j-1)) * x $$ (\<v>-h-1,0))^2) =
      of_int \<Lambda> * (\<Sum>j \<in> {0..<\<v>}.(x $$ (j, 0)))^2 +
      of_int (\<k> - \<Lambda>) * (\<Sum>j \<in> {0..<\<v>}. (x $$ (j, 0))^2)"
      using base by simp

    then have "(\<Sum>j \<in> {0..<4}.(\<Sum>h \<in> {0..<\<v>}. of_int(N $$ (\<v>-h-1,\<v>-j-1)) * x $$ (\<v>-h-1,0))^2) +
      (\<Sum>j \<in> {4..<\<v>}.(\<Sum>h \<in> {0..<\<v>}. of_int(N $$ (\<v>-h-1,\<v>-j-1)) * x $$ (\<v>-h-1,0))^2) =
       of_int \<Lambda> * (\<Sum>j \<in> {0..<\<v>}.(x $$ (j, 0)))^2 +
       of_int (\<k> - \<Lambda>) * (\<Sum>j \<in> {0..<\<v>}. (x $$ (j, 0))^2)"
      using trick2 by simp

    then have "(\<Sum>j \<in> {0..<4}.(\<Sum>h \<in> {0..<\<v>}. of_int(N $$ (\<v>-h-1,\<v>-j-1)) * x $$ (\<v>-h-1,0))^2) +
      (\<Sum>j \<in> {4..<\<v>}.(\<Sum>h \<in> {0..<\<v>}. of_int(N $$ (\<v>-h-1,\<v>-j-1)) * x $$ (\<v>-h-1,0))^2) =
       of_int \<Lambda> * (\<Sum>j \<in> {0..<\<v>}.(x $$ (j, 0)))^2 +
       of_int (\<k> - \<Lambda>) * (\<Sum>j \<in> {0..<4}. (x $$ (j, 0))^2) +
       of_int (\<k> - \<Lambda>) * (\<Sum>j \<in> {4..<\<v>}. (x $$ (j, 0))^2)"
      using trick3 by simp

  have "(\<Sum>j \<in> {4..<m}. ((\<Sum>h \<in> {0..<m}. 
        of_int(N $$ (m-h-1,m-j-1)) * x $$ (m-h-1,0)) +
        (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-j-1)) * x $$ (h,0)))^2) =
         of_int \<Lambda> * (\<Sum>j \<in> {0..<\<v>}.(x $$ (j, 0)))^2 +
         of_int (\<k> - \<Lambda>) * (\<Sum>j \<in> {4..<m}. (x $$ (m-j-1, 0))^2)"
  proof (induction n)
    case 0
    have "(\<Sum>j \<in> {0..<4}.(\<Sum>h \<in> {0..<\<v>}. of_int(N $$ (\<v>-h-1,\<v>-j-1)) * x $$ (\<v>-h-1,0))) = 
          ?L0^2 + ?L1^2 + ?L2^2 + ?L3^2"
      using sumdef by simp





    then show ?case 
      using base by auto
  next
    case (Suc n) 
    have split2: "{0..<\<v>} = {0..<m} \<union> {m..<\<v>}" using ineq by auto
    have inter2: "{} = {0..<m} \<inter> {m..<\<v>}" by auto
    have split_sum: "(\<Sum>h \<in> {0..<\<v>}. of_int(N $$ (h,\<v>-j-1)) * x $$ (h,0)) =
          (\<Sum>h \<in> {0..<m}. of_int(N $$ (h,\<v>-j-1)) * x $$ (h,0)) +
          (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,\<v>-j-1)) * x $$ (h,0))"
     using split2 inter2 sum.union_disjoint[of "{0..<m}" "{m..<\<v>}" "\<lambda> h . 
      (of_int(N $$ (h,\<v>-j-1)) * x $$ (h,0))"] 
     by (metis (no_types, lifting) finite_atLeastLessThan)
 

 

   then show ?thesis by simp
 qed
  oops
qed

end