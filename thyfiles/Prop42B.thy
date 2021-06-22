theory Prop42B
	imports Axioms Definitions Theorems
begin

theorem Prop42B:
	assumes: `axioms`
		"triangle a b c"
		"midpoint b e c"
		"\<not> col J D K"
		"midpoint B E C"
		"seg_eq E C e c"
		"\<not> col R E C"
	shows: "\<exists> F G. parallelogram F E C G \<and> qua_eq_area a b e c F E C G \<and> ang_eq C E F J D K \<and> same_side R F E C"
proof -
	have "bet B E C \<and> seg_eq B E E C" using midpoint_f[OF `axioms` `midpoint B E C`] .
	have "bet B E C" using `bet B E C \<and> seg_eq B E E C` by blast
	have "bet b e c \<and> seg_eq b e e c" using midpoint_f[OF `axioms` `midpoint b e c`] .
	have "bet b e c" using `bet b e c \<and> seg_eq b e e c` by blast
	have "seg_eq b e e c" using `bet b e c \<and> seg_eq b e e c` by blast
	have "B \<noteq> C" using betweennotequal[OF `axioms` `bet B E C`] by blast
	have "\<not> col a b c" using triangle_f[OF `axioms` `triangle a b c`] .
	have "\<not> col E C R" using NCorder[OF `axioms` `\<not> col R E C`] by blast
	have "col B E C" using collinear_b `axioms` `bet B E C \<and> seg_eq B E E C` by blast
	have "col E C B" using collinearorder[OF `axioms` `col B E C`] by blast
	have "C = C" using equalityreflexiveE[OF `axioms`] .
	have "col E C C" using collinear_b `axioms` `C = C` by blast
	have "\<not> col B C R" using NChelper[OF `axioms` `\<not> col E C R` `col E C B` `col E C C` `B \<noteq> C`] .
	obtain H P where "ray_on B C H \<and> ang_eq P B H a b c \<and> same_side P R B C" using Prop23C[OF `axioms` `B \<noteq> C` `\<not> col a b c` `\<not> col B C R`]  by  blast
	have "ray_on B C H" using `ray_on B C H \<and> ang_eq P B H a b c \<and> same_side P R B C` by blast
	have "ang_eq P B H a b c" using `ray_on B C H \<and> ang_eq P B H a b c \<and> same_side P R B C` by blast
	have "same_side P R B C" using `ray_on B C H \<and> ang_eq P B H a b c \<and> same_side P R B C` by blast
	have "seg_eq E C e c" using `seg_eq E C e c` .
	have "seg_eq B E E C" using `bet B E C \<and> seg_eq B E E C` by blast
	have "seg_eq B E e c" using congruencetransitive[OF `axioms` `seg_eq B E E C` `seg_eq E C e c`] .
	have "seg_eq E C B E" using congruencesymmetric[OF `axioms` `seg_eq B E E C`] .
	have "seg_eq E C e c" using congruencetransitive[OF `axioms` `seg_eq E C B E` `seg_eq B E e c`] .
	have "seg_eq B E e c" using congruencetransitive[OF `axioms` `seg_eq B E E C` `seg_eq E C e c`] .
	have "seg_eq e c b e" using congruencesymmetric[OF `axioms` `seg_eq b e e c`] .
	have "seg_eq B E b e" using congruencetransitive[OF `axioms` `seg_eq B E e c` `seg_eq e c b e`] .
	have "seg_eq B C b c" using sumofparts[OF `axioms` `seg_eq B E b e` `seg_eq E C e c` `bet B E C` `bet b e c`] .
	have "ang_eq a b c P B H" using equalanglessymmetric[OF `axioms` `ang_eq P B H a b c`] .
	have "ray_on B H C" using ray5[OF `axioms` `ray_on B C H`] .
	have "\<not> col B C P" using sameside_f[OF `axioms` `same_side P R B C`] by blast
	have "B \<noteq> P" using NCdistinct[OF `axioms` `\<not> col B C P`] by blast
	have "\<not> col a b c" using triangle_f[OF `axioms` `triangle a b c`] .
	have "b \<noteq> a" using NCdistinct[OF `axioms` `\<not> col a b c`] by blast
	obtain A where "ray_on B P A \<and> seg_eq B A b a" using layoff[OF `axioms` `B \<noteq> P` `b \<noteq> a`] by blast
	have "ray_on B P A" using `ray_on B P A \<and> seg_eq B A b a` by blast
	have "seg_eq B A b a" using `ray_on B P A \<and> seg_eq B A b a` by blast
	have "ang_eq a b c A B C" using equalangleshelper[OF `axioms` `ang_eq a b c P B H` `ray_on B P A` `ray_on B H C`] .
	have "ang_eq A B C a b c" using equalanglessymmetric[OF `axioms` `ang_eq a b c A B C`] .
	have "\<not> col A B C" using equalanglesNC[OF `axioms` `ang_eq a b c A B C`] .
	have "triangle A B C" using triangle_b[OF `axioms` `\<not> col A B C`] .
	have "seg_eq A C a c" using Prop04[OF `axioms` `seg_eq B A b a` `seg_eq B C b c` `ang_eq A B C a b c`] by blast
	have "seg_eq A B a b" using congruenceflip[OF `axioms` `seg_eq B A b a`] by blast
	have "seg_eq B A b a" using `seg_eq B A b a` .
	have "seg_eq C A c a" using congruenceflip[OF `axioms` `seg_eq A C a c`] by blast
	have "seg_eq B E b e" using `seg_eq B E b e` .
	have "seg_eq E A e a" using interior5[OF `axioms` `bet B E C` `bet b e c` `seg_eq B E b e` `seg_eq E C e c` `seg_eq B A b a` `seg_eq C A c a`] .
	have "seg_eq A E a e" using congruenceflip[OF `axioms` `seg_eq E A e a`] by blast
	have "seg_eq A B a b" using `seg_eq A B a b` .
	have "seg_eq E B e b" using congruenceflip[OF `axioms` `seg_eq B E b e`] by blast
	have "col B E C" using collinear_b `axioms` `bet B E C \<and> seg_eq B E E C` by blast
	have "col B C E" using collinearorder[OF `axioms` `col B E C`] by blast
	have "\<not> col B C A" using NCorder[OF `axioms` `\<not> col A B C`] by blast
	have "B = B" using equalityreflexiveE[OF `axioms`] .
	have "col B C B" using collinear_b `axioms` `B = B` by blast
	have "B \<noteq> E" using betweennotequal[OF `axioms` `bet B E C`] by blast
	have "\<not> col B E A" using NChelper[OF `axioms` `\<not> col B C A` `col B C B` `col B C E` `B \<noteq> E`] .
	have "\<not> col A E B" using NCorder[OF `axioms` `\<not> col B E A`] by blast
	have "col b e c" using collinear_b `axioms` `bet b e c \<and> seg_eq b e e c` by blast
	have "col b c e" using collinearorder[OF `axioms` `col b e c`] by blast
	have "\<not> col b c a" using NCorder[OF `axioms` `\<not> col a b c`] by blast
	have "b = b" using equalityreflexiveE[OF `axioms`] .
	have "col b c b" using collinear_b `axioms` `b = b` by blast
	have "b \<noteq> e" using betweennotequal[OF `axioms` `bet b e c`] by blast
	have "\<not> col b e a" using NChelper[OF `axioms` `\<not> col b c a` `col b c b` `col b c e` `b \<noteq> e`] .
	have "\<not> col a e b" using NCorder[OF `axioms` `\<not> col b e a`] by blast
	have "triangle A E B" using triangle_b[OF `axioms` `\<not> col A E B`] .
	have "tri_cong A E B a e b" using trianglecongruence_b[OF `axioms` `seg_eq A E a e` `seg_eq E B e b` `seg_eq A B a b` `triangle A E B`] .
	have "tri_eq_area A E B a e b" using congruentequalE[OF `axioms` `tri_cong A E B a e b`] .
	have "seg_eq A C a c" using `seg_eq A C a c` .
	have "seg_eq E C e c" using `seg_eq E C e c` .
	have "col C B E" using collinearorder[OF `axioms` `col B C E`] by blast
	have "E \<noteq> C" using betweennotequal[OF `axioms` `bet B E C`] by blast
	have "C \<noteq> E" using inequalitysymmetric[OF `axioms` `E \<noteq> C`] .
	have "\<not> col C B A" using NCorder[OF `axioms` `\<not> col A B C`] by blast
	have "C = C" using equalityreflexiveE[OF `axioms`] .
	have "col C B C" using collinear_b `axioms` `C = C` by blast
	have "\<not> col C E A" using NChelper[OF `axioms` `\<not> col C B A` `col C B C` `col C B E` `C \<noteq> E`] .
	have "\<not> col A E C" using NCorder[OF `axioms` `\<not> col C E A`] by blast
	have "triangle A E C" using triangle_b[OF `axioms` `\<not> col A E C`] .
	have "tri_cong A E C a e c" using trianglecongruence_b[OF `axioms` `seg_eq A E a e` `seg_eq E C e c` `seg_eq A C a c` `triangle A E C`] .
	have "tri_eq_area A E C a e c" using congruentequalE[OF `axioms` `tri_cong A E C a e c`] .
	have "E = E" using equalityreflexiveE[OF `axioms`] .
	have "col A E E" using collinear_b `axioms` `E = E` by blast
	have "oppo_side B A E C" using oppositeside_b[OF `axioms` `bet B E C` `col A E E` `\<not> col A E B`] .
	have "e = e" using equalityreflexiveE[OF `axioms`] .
	have "col a e e" using collinear_b `axioms` `e = e` by blast
	have "oppo_side b a e c" using oppositeside_b[OF `axioms` `bet b e c` `col a e e` `\<not> col a e b`] .
	have "qua_eq_area A B E C a b e c" sorry
	have "qua_eq_area a b e c A B E C" using EFsymmetricE[OF `axioms` `qua_eq_area A B E C a b e c`] .
	obtain F G where "parallelogram F E C G \<and> qua_eq_area A B E C F E C G \<and> ang_eq C E F J D K \<and> col F G A" using Prop42[OF `axioms` `triangle A B C` `\<not> col J D K` `midpoint B E C`]  by  blast
	have "parallelogram F E C G" using `parallelogram F E C G \<and> qua_eq_area A B E C F E C G \<and> ang_eq C E F J D K \<and> col F G A` by blast
	have "qua_eq_area A B E C F E C G" using `parallelogram F E C G \<and> qua_eq_area A B E C F E C G \<and> ang_eq C E F J D K \<and> col F G A` by blast
	have "qua_eq_area a b e c F E C G" using EFtransitiveE[OF `axioms` `qua_eq_area a b e c A B E C` `qua_eq_area A B E C F E C G`] .
	have "ang_eq C E F J D K" using `parallelogram F E C G \<and> qua_eq_area A B E C F E C G \<and> ang_eq C E F J D K \<and> col F G A` by blast
	have "same_side P R B C" using `same_side P R B C` .
	have "ray_on B P A" using `ray_on B P A` .
	have "col C B E" using `col C B E` .
	have "C \<noteq> E" using `C \<noteq> E` .
	have "same_side R P B C" using samesidesymmetric[OF `axioms` `same_side P R B C`] by blast
	have "col B B C" using collinear_b `axioms` `B = B` by blast
	have "same_side R A B C" using sameside2[OF `axioms` `same_side R P B C` `col B B C` `ray_on B P A`] .
	have "same_side R A C B" using samesideflip[OF `axioms` `same_side R A B C`] .
	have "same_side R A C E" using samesidecollinear[OF `axioms` `same_side R A C B` `col C B E` `C \<noteq> E`] .
	have "same_side A R C E" using samesidesymmetric[OF `axioms` `same_side R A C E`] by blast
	have "same_side A R E C" using samesideflip[OF `axioms` `same_side A R C E`] .
	have "col F G A" using `parallelogram F E C G \<and> qua_eq_area A B E C F E C G \<and> ang_eq C E F J D K \<and> col F G A` by blast
	have "col G F A" using collinearorder[OF `axioms` `col F G A`] by blast
	have "parallel F G E C" using parallelogram_f[OF `axioms` `parallelogram F E C G`] by blast
	have "parallel E C F G" using parallelsymmetric[OF `axioms` `parallel F G E C`] .
	have "parallel E C G F" using parallelflip[OF `axioms` `parallel E C F G`] by blast
	consider "A = F"|"A \<noteq> F" by blast
	hence same_side R F E C
	proof (cases)
		case 1
		have "same_side R A E C" using samesideflip[OF `axioms` `same_side R A C E`] .
		have "same_side R F E C" using `same_side R A E C` `A = F` by blast
	next
		case 2
		have "parallel E C A F" using collinearparallel[OF `axioms` `parallel E C G F` `col G F A` `A \<noteq> F`] .
		have "parallel E C F A" using parallelflip[OF `axioms` `parallel E C A F`] by blast
		have "tarski_parallel E C F A" using paralleldef2B[OF `axioms` `parallel E C F A`] .
		have "same_side F A E C" using tarski_parallel_f[OF `axioms` `tarski_parallel E C F A`] by blast
		have "same_side F R E C" using samesidetransitive[OF `axioms` `same_side F A E C` `same_side A R E C`] .
		have "same_side R F E C" using samesidesymmetric[OF `axioms` `same_side F R E C`] by blast
	next
	have "parallelogram F E C G \<and> qua_eq_area a b e c F E C G \<and> ang_eq C E F J D K \<and> same_side R F E C" using `parallelogram F E C G \<and> qua_eq_area A B E C F E C G \<and> ang_eq C E F J D K \<and> col F G A` `qua_eq_area a b e c F E C G` `parallelogram F E C G \<and> qua_eq_area A B E C F E C G \<and> ang_eq C E F J D K \<and> col F G A` `same_side R F E C` by blast
	thus ?thesis by blast
qed

end