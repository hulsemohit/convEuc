theory Prop22
	imports Axioms Definitions Theorems
begin

theorem Prop22:
	assumes: `axioms`
		"seg_sum_gt A a B b C c"
		"seg_sum_gt A a C c B b"
		"seg_sum_gt B b C c A a"
		"F \<noteq> E"
	shows: "\<exists> G K. seg_eq F G B b \<and> seg_eq F K A a \<and> seg_eq G K C c \<and> ray_on F E G \<and> triangle F G K"
proof -
	obtain P where "bet A a P \<and> seg_eq a P B b \<and> seg_lt C c A P" using togethergreater_f[OF `axioms` `seg_sum_gt A a B b C c`] by blast
	have "bet A a P" using `bet A a P \<and> seg_eq a P B b \<and> seg_lt C c A P` by blast
	have "seg_eq a P B b" using `bet A a P \<and> seg_eq a P B b \<and> seg_lt C c A P` by blast
	have "seg_lt C c A P" using `bet A a P \<and> seg_eq a P B b \<and> seg_lt C c A P` by blast
	have "A \<noteq> a" using betweennotequal[OF `axioms` `bet A a P`] by blast
	have "a \<noteq> P" using betweennotequal[OF `axioms` `bet A a P`] by blast
	have "B \<noteq> b" using nullsegment3[OF `axioms` `a \<noteq> P` `seg_eq a P B b`] .
	have "C \<noteq> c" using lessthannotequal[OF `axioms` `seg_lt C c A P`] by blast
	obtain G where "ray_on F E G \<and> seg_eq F G B b" using layoff[OF `axioms` `F \<noteq> E` `B \<noteq> b`] by blast
	have "ray_on F E G" using `ray_on F E G \<and> seg_eq F G B b` by blast
	have "seg_eq F G B b" using `ray_on F E G \<and> seg_eq F G B b` by blast
	have "seg_eq B b F G" using congruencesymmetric[OF `axioms` `seg_eq F G B b`] .
	have "F \<noteq> G" using nullsegment3[OF `axioms` `B \<noteq> b` `seg_eq B b F G`] .
	have "G \<noteq> F" using inequalitysymmetric[OF `axioms` `F \<noteq> G`] .
	obtain H where "bet F G H \<and> seg_eq G H C c" using extensionE[OF `axioms` `F \<noteq> G` `C \<noteq> c`] by blast
	have "bet F G H" using `bet F G H \<and> seg_eq G H C c` by blast
	obtain D where "bet G F D \<and> seg_eq F D A a" using extensionE[OF `axioms` `G \<noteq> F` `A \<noteq> a`] by blast
	have "bet G F D" using `bet G F D \<and> seg_eq F D A a` by blast
	have "seg_eq F D A a" using `bet G F D \<and> seg_eq F D A a` by blast
	have "seg_eq D F A a" using congruenceflip[OF `axioms` `seg_eq F D A a`] by blast
	have "bet D F G" using betweennesssymmetryE[OF `axioms` `bet G F D`] .
	obtain L where "circle L F A a" using circle_f[OF `axioms` `A \<noteq> a`] by blast
	obtain R where "circle R G C c" using circle_f[OF `axioms` `C \<noteq> c`] by blast
	have "seg_eq G H C c" using `bet F G H \<and> seg_eq G H C c` by blast
	have "circle R G C c \<and> cir_on H R" using on_b[OF `axioms` `circle R G C c` `seg_eq G H C c`] .
	have "seg_eq F G B b" using `seg_eq F G B b` .
	have "seg_eq G H C c" using `seg_eq G H C c` .
	have "seg_eq D F A a" using `seg_eq D F A a` .
	have "seg_sum_gt B b C c A a" using `seg_sum_gt B b C c A a` .
	have "seg_lt D F F H" using together[OF `axioms` `seg_sum_gt B b C c A a` `seg_eq F G B b` `seg_eq G H C c` `bet F G H` `seg_eq D F A a`] by blast
	obtain M where "bet F M H \<and> seg_eq F M D F" using lessthan_f[OF `axioms` `seg_lt D F F H`] by blast
	have "bet F M H" using `bet F M H \<and> seg_eq F M D F` by blast
	have "seg_eq F M D F" using `bet F M H \<and> seg_eq F M D F` by blast
	have "seg_eq D F A a" using `seg_eq D F A a` .
	have "seg_eq F M A a" using congruencetransitive[OF `axioms` `seg_eq F M D F` `seg_eq D F A a`] .
	have "circle L F A a \<and> cir_ou H L" using outside_b[OF `axioms` `circle L F A a` `bet F M H` `seg_eq F M A a`] .
	have "seg_sum_gt A a B b C c" using `seg_sum_gt A a B b C c` .
	have "seg_eq D F A a" using `seg_eq D F A a` .
	have "seg_eq F G B b" using `seg_eq F G B b` .
	have "bet D F G" using `bet D F G` .
	have "seg_eq C c C c" using congruencereflexiveE[OF `axioms`] by blast
	have "seg_lt C c D G" using together[OF `axioms` `seg_sum_gt A a B b C c` `seg_eq D F A a` `seg_eq F G B b` `bet D F G` `seg_eq C c C c`] by blast
	have "seg_eq D G G D" using equalityreverseE[OF `axioms`] by blast
	have "seg_lt C c G D" using lessthancongruence[OF `axioms` `seg_lt C c D G` `seg_eq D G G D`] .
	obtain N where "bet G N D \<and> seg_eq G N C c" using lessthan_f[OF `axioms` `seg_lt C c G D`] by blast
	have "bet G N D" using `bet G N D \<and> seg_eq G N C c` by blast
	have "bet D F G" using `bet D F G` .
	have "bet F G H" using `bet F G H` .
	have "bet D F H" using n3_7b[OF `axioms` `bet D F G` `bet F G H`] .
	have "bet F M H" using `bet F M H` .
	have "bet D F M" using innertransitivityE[OF `axioms` `bet D F H` `bet F M H`] .
	have "seg_eq F D A a" using congruenceflip[OF `axioms` `seg_eq D F A a`] by blast
	have "bet D N G" using betweennesssymmetryE[OF `axioms` `bet G N D`] .
	have "F \<noteq> M" using betweennotequal[OF `axioms` `bet D F M`] by blast
	obtain J where "bet F M J \<and> seg_eq M J C c" using extensionE[OF `axioms` `F \<noteq> M` `C \<noteq> c`] by blast
	have "bet F M J" using `bet F M J \<and> seg_eq M J C c` by blast
	have "bet D F M" using `bet D F M` .
	have "bet D F J" using n3_7b[OF `axioms` `bet D F M` `bet F M J`] .
	have "seg_eq F G B b" using `seg_eq F G B b` .
	have "seg_eq F M A a" using `seg_eq F M A a` .
	have "seg_eq M J C c" using `bet F M J \<and> seg_eq M J C c` by blast
	have "seg_sum_gt A a C c B b" using `seg_sum_gt A a C c B b` .
	have "seg_lt F G F J \<and> A \<noteq> a \<and> C \<noteq> c \<and> B \<noteq> b" using together[OF `axioms` `seg_sum_gt A a C c B b` `seg_eq F M A a` `seg_eq M J C c` `bet F M J` `seg_eq F G B b`] .
	have "seg_lt F G F J" using `seg_lt F G F J \<and> A \<noteq> a \<and> C \<noteq> c \<and> B \<noteq> b` by blast
	obtain Q where "bet F Q J \<and> seg_eq F Q F G" using lessthan_f[OF `axioms` `seg_lt F G F J`] by blast
	have "bet F Q J" using `bet F Q J \<and> seg_eq F Q F G` by blast
	have "seg_eq F Q F G" using `bet F Q J \<and> seg_eq F Q F G` by blast
	have "F \<noteq> J" using betweennotequal[OF `axioms` `bet D F J`] by blast
	have "ray_on F J Q" using ray4 `axioms` `bet F Q J \<and> seg_eq F Q F G` `F \<noteq> J` by blast
	have "bet D F G" using `bet D F G` .
	have "bet D F J" using `bet D F J` .
	have "ray_on F G J" using ray_b[OF `axioms` `bet D F J` `bet D F G`] .
	have "ray_on F J G" using ray5[OF `axioms` `ray_on F G J`] .
	have "Q = G" using layoffunique[OF `axioms` `ray_on F J Q` `ray_on F J G` `seg_eq F Q F G`] .
	have "G = Q" using equalitysymmetric[OF `axioms` `Q = G`] .
	have "bet F G J" using `bet F Q J` `Q = G` by blast
	have "bet D F G" using `bet D F G` .
	have "bet D G J" using n3_7a[OF `axioms` `bet D F G` `bet F G J`] .
	have "seg_eq G N C c" using `bet G N D \<and> seg_eq G N C c` by blast
	have "seg_eq M J C c" using `seg_eq M J C c` .
	have "seg_eq C c M J" using congruencesymmetric[OF `axioms` `seg_eq M J C c`] .
	have "seg_eq G N M J" using congruencetransitive[OF `axioms` `seg_eq G N C c` `seg_eq C c M J`] .
	have "seg_eq N G M J" using congruenceflip[OF `axioms` `seg_eq G N M J`] by blast
	have "bet D M J" using n3_7a[OF `axioms` `bet D F M` `bet F M J`] .
	have "bet D N G" using `bet D N G` .
	have "bet D N M" using subtractequals[OF `axioms` `bet D N G` `bet D M J` `seg_eq N G M J` `bet D G J`] .
	have "seg_eq F M A a" using `seg_eq F M A a` .
	have "seg_eq G N C c" using `seg_eq G N C c` .
	have "circle L F A a \<and> cir_in N L" using inside_b[OF `axioms` `circle L F A a` `bet D F M` `seg_eq F M A a` `seg_eq F D A a` `bet D N M`] .
	have "circle R G C c \<and> cir_on N R" using on_b[OF `axioms` `circle R G C c` `seg_eq G N C c`] .
	have "cir_on N R" using `circle R G C c \<and> cir_on N R` by blast
	have "cir_on H R" using `circle R G C c \<and> cir_on H R` by blast
	have "cir_ou H L" using `circle L F A a \<and> cir_ou H L` by blast
	have "cir_in N L" using `circle L F A a \<and> cir_in N L` by blast
	obtain K where "cir_on K L \<and> cir_on K R" using circle-circleE[OF `axioms` `circle L F A a` `cir_in N L` `cir_ou H L` `circle R G C c` `cir_on N R` `cir_on H R`] by blast
	have "cir_on K L" using `cir_on K L \<and> cir_on K R` by blast
	have "cir_on K R" using `cir_on K L \<and> cir_on K R` by blast
	have "seg_eq F K A a" using on_f[OF `axioms` `circle L F A a` `cir_on K L`] by blast
	have "seg_eq G K C c" using on_f[OF `axioms` `circle R G C c` `cir_on K R`] by blast
	have "\<not> (col F G K)"
	proof (rule ccontr)
		assume "col F G K"
		have "F = G \<or> F = K \<or> G = K \<or> bet G F K \<or> bet F G K \<or> bet F K G" using collinear_f[OF `axioms` `col F G K`] .
		consider "F = G"|"F = K"|"G = K"|"bet G F K"|"bet F G K"|"bet F K G" using `F = G \<or> F = K \<or> G = K \<or> bet G F K \<or> bet F G K \<or> bet F K G`  by blast
		hence \<not> col F G K
		proof (cases)
			case 1
			have "\<not> (col F G K)"
			proof (rule ccontr)
				assume "col F G K"
				have "F \<noteq> G" using `F \<noteq> G` .
				show "False" using `F \<noteq> G` `F = G` by blast
			qed
			hence "\<not> col F G K" by blast
		next
			case 2
			have "seg_eq F K A a" using `seg_eq F K A a` .
			have "A \<noteq> a" using `A \<noteq> a` .
			have "seg_eq A a F K" using congruencesymmetric[OF `axioms` `seg_eq F K A a`] .
			have "\<not> (col F G K)"
			proof (rule ccontr)
				assume "col F G K"
				have "F \<noteq> K" using nullsegment3[OF `axioms` `A \<noteq> a` `seg_eq A a F K`] .
				show "False" using `F \<noteq> K` `F = K` by blast
			qed
			hence "\<not> col F G K" by blast
		next
			case 3
			have "seg_eq G K C c" using `seg_eq G K C c` .
			have "seg_eq C c G K" using congruencesymmetric[OF `axioms` `seg_eq G K C c`] .
			have "\<not> (col F G K)"
			proof (rule ccontr)
				assume "col F G K"
				have "C \<noteq> c" using `C \<noteq> c` .
				have "G \<noteq> K" using nullsegment3[OF `axioms` `C \<noteq> c` `seg_eq C c G K`] .
				show "False" using `G \<noteq> K` `G = K` by blast
			qed
			hence "\<not> col F G K" by blast
		next
			case 4
			have "bet K F G" using betweennesssymmetryE[OF `axioms` `bet G F K`] .
			have "seg_eq F K A a" using `seg_eq F K A a` .
			have "seg_eq K F A a" using congruenceflip[OF `axioms` `seg_eq F K A a`] by blast
			have "seg_eq G K C c" using `seg_eq G K C c` .
			have "seg_sum_gt A a B b C c" using `seg_sum_gt A a B b C c` .
			obtain S where "bet A a S \<and> seg_eq a S B b \<and> seg_lt C c A S" using togethergreater_f[OF `axioms` `seg_sum_gt A a B b C c`] by blast
			have "seg_eq a S B b" using `bet A a S \<and> seg_eq a S B b \<and> seg_lt C c A S` by blast
			have "seg_lt C c A S" using `bet A a S \<and> seg_eq a S B b \<and> seg_lt C c A S` by blast
			have "seg_eq A a K F" using congruencesymmetric[OF `axioms` `seg_eq K F A a`] .
			have "seg_eq a S F G" using congruencetransitive[OF `axioms` `seg_eq a S B b` `seg_eq B b F G`] .
			have "bet A a S" using `bet A a S \<and> seg_eq a S B b \<and> seg_lt C c A S` by blast
			have "bet K F G" using `bet K F G` .
			have "seg_eq A S K G" using sumofparts[OF `axioms` `seg_eq A a K F` `seg_eq a S F G` `bet A a S` `bet K F G`] .
			have "seg_eq A S G K" using congruenceflip[OF `axioms` `seg_eq A S K G`] by blast
			have "seg_lt C c G K" using lessthancongruence[OF `axioms` `seg_lt C c A S` `seg_eq A S G K`] .
			have "seg_eq C c G K" using congruencesymmetric[OF `axioms` `seg_eq G K C c`] .
			have "seg_lt G K G K" using lessthancongruence2[OF `axioms` `seg_lt C c G K` `seg_eq C c G K`] .
			have "\<not> (col F G K)"
			proof (rule ccontr)
				assume "col F G K"
				have "\<not> (seg_lt G K G K)" using trichotomy2[OF `axioms` `seg_lt G K G K`] .
				show "False" using `\<not> (seg_lt G K G K)` `seg_lt G K G K` by blast
			qed
			hence "\<not> col F G K" by blast
		next
			case 5
			have "seg_eq F K A a" using `seg_eq F K A a` .
			have "seg_eq G K C c" using `seg_eq G K C c` .
			have "seg_eq F G B b" using `seg_eq F G B b` .
			have "seg_sum_gt B b C c A a" using `seg_sum_gt B b C c A a` .
			obtain S where "bet B b S \<and> seg_eq b S C c \<and> seg_lt A a B S" using togethergreater_f[OF `axioms` `seg_sum_gt B b C c A a`] by blast
			have "bet B b S" using `bet B b S \<and> seg_eq b S C c \<and> seg_lt A a B S` by blast
			have "seg_eq b S C c" using `bet B b S \<and> seg_eq b S C c \<and> seg_lt A a B S` by blast
			have "seg_lt A a B S" using `bet B b S \<and> seg_eq b S C c \<and> seg_lt A a B S` by blast
			have "seg_eq C c b S" using congruencesymmetric[OF `axioms` `seg_eq b S C c`] .
			have "seg_eq G K b S" using congruencetransitive[OF `axioms` `seg_eq G K C c` `seg_eq C c b S`] .
			have "seg_eq F K B S" using sumofparts[OF `axioms` `seg_eq F G B b` `seg_eq G K b S` `bet F G K` `bet B b S`] .
			have "seg_eq A a F K" using congruencesymmetric[OF `axioms` `seg_eq F K A a`] .
			have "seg_lt F K B S" using lessthancongruence2[OF `axioms` `seg_lt A a B S` `seg_eq A a F K`] .
			have "seg_eq B S F K" using congruencesymmetric[OF `axioms` `seg_eq F K B S`] .
			have "seg_lt F K F K" using lessthancongruence[OF `axioms` `seg_lt F K B S` `seg_eq B S F K`] .
			have "\<not> (col F G K)"
			proof (rule ccontr)
				assume "col F G K"
				have "\<not> (seg_lt F K F K)" using trichotomy2[OF `axioms` `seg_lt F K F K`] .
				show "False" using `\<not> (seg_lt F K F K)` `seg_lt F K F K` by blast
			qed
			hence "\<not> col F G K" by blast
		next
			case 6
			have "seg_eq F K A a" using `seg_eq F K A a` .
			have "seg_eq G K C c" using `seg_eq G K C c` .
			have "seg_sum_gt A a C c B b" using `seg_sum_gt A a C c B b` .
			obtain S where "bet A a S \<and> seg_eq a S C c \<and> seg_lt B b A S" using togethergreater_f[OF `axioms` `seg_sum_gt A a C c B b`] by blast
			have "bet A a S" using `bet A a S \<and> seg_eq a S C c \<and> seg_lt B b A S` by blast
			have "seg_eq a S C c" using `bet A a S \<and> seg_eq a S C c \<and> seg_lt B b A S` by blast
			have "seg_lt B b A S" using `bet A a S \<and> seg_eq a S C c \<and> seg_lt B b A S` by blast
			have "seg_lt F G A S" using lessthancongruence2[OF `axioms` `seg_lt B b A S` `seg_eq B b F G`] .
			have "seg_eq C c a S" using congruencesymmetric[OF `axioms` `seg_eq a S C c`] .
			have "seg_eq G K a S" using congruencetransitive[OF `axioms` `seg_eq G K C c` `seg_eq C c a S`] .
			have "seg_eq K G a S" using congruenceflip[OF `axioms` `seg_eq G K a S`] by blast
			have "seg_eq F G A S" using sumofparts[OF `axioms` `seg_eq F K A a` `seg_eq K G a S` `bet F K G` `bet A a S`] .
			have "seg_eq A S F G" using congruencesymmetric[OF `axioms` `seg_eq F G A S`] .
			have "seg_lt F G F G" using lessthancongruence[OF `axioms` `seg_lt F G A S` `seg_eq A S F G`] .
			have "\<not> (col F G K)"
			proof (rule ccontr)
				assume "col F G K"
				have "\<not> (seg_lt F G F G)" using trichotomy2[OF `axioms` `seg_lt F G F G`] .
				show "False" using `\<not> (seg_lt F G F G)` `seg_lt F G F G` by blast
			qed
			hence "\<not> col F G K" by blast
		next
		show "False" using `\<not> col F G K` `col F G K` by blast
	qed
	hence "\<not> col F G K" by blast
	have "triangle F G K" using triangle_b[OF `axioms` `\<not> col F G K`] .
	have "seg_eq F G B b \<and> seg_eq F K A a \<and> seg_eq G K C c \<and> ray_on F E G \<and> triangle F G K" using `ray_on F E G \<and> seg_eq F G B b` `seg_eq F K A a` `seg_eq G K C c` `ray_on F E G \<and> seg_eq F G B b` `triangle F G K` by blast
	thus ?thesis by blast
qed

end