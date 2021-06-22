theory Prop44
	imports Axioms Definitions Theorems
begin

theorem Prop44:
	assumes: `axioms`
		"triangle a b c"
		"\<not> col J D N"
		"\<not> col A B R"
	shows: "\<exists> L M m. parallelogram A B M L \<and> ang_eq A B M J D N \<and> qua_eq_area a b m c A B M L \<and> midpoint b m c \<and> oppo_side M A B R"
proof -
	have "A \<noteq> B" using NCdistinct[OF `axioms` `\<not> col A B R`] by blast
	have "\<not> col a b c" using triangle_f[OF `axioms` `triangle a b c`] .
	have "b \<noteq> c" using NCdistinct[OF `axioms` `\<not> col a b c`] by blast
	obtain m where "bet b m c \<and> seg_eq m b m c" using Prop10[OF `axioms` `b \<noteq> c`] by blast
	have "bet b m c" using `bet b m c \<and> seg_eq m b m c` by blast
	have "seg_eq m b m c" using `bet b m c \<and> seg_eq m b m c` by blast
	have "seg_eq b m m c" using congruenceflip[OF `axioms` `seg_eq m b m c`] by blast
	have "midpoint b m c" using midpoint_b[OF `axioms` `bet b m c` `seg_eq b m m c`] .
	have "m \<noteq> c" using betweennotequal[OF `axioms` `bet b m c`] by blast
	obtain E where "bet A B E \<and> seg_eq B E m c" using extensionE[OF `axioms` `A \<noteq> B` `m \<noteq> c`] by blast
	have "bet A B E" using `bet A B E \<and> seg_eq B E m c` by blast
	have "seg_eq B E m c" using `bet A B E \<and> seg_eq B E m c` by blast
	have "B \<noteq> E" using betweennotequal[OF `axioms` `bet A B E`] by blast
	have "col A B E" using collinear_b `axioms` `bet A B E \<and> seg_eq B E m c` by blast
	have "col B A E" using collinearorder[OF `axioms` `col A B E`] by blast
	have "B = B" using equalityreflexiveE[OF `axioms`] .
	have "col B A B" using collinear_b `axioms` `B = B` by blast
	have "\<not> col B A R" using NCorder[OF `axioms` `\<not> col A B R`] by blast
	have "\<not> col B E R" using NChelper[OF `axioms` `\<not> col B A R` `col B A B` `col B A E` `B \<noteq> E`] .
	obtain e g where "ray_on B E e \<and> ang_eq g B e J D N \<and> same_side g R B E" using Prop23C[OF `axioms` `B \<noteq> E` `\<not> col J D N` `\<not> col B E R`]  by  blast
	have "B \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> B`] .
	obtain P where "bet B A P \<and> seg_eq A P B A" using extensionE[OF `axioms` `B \<noteq> A` `B \<noteq> A`] by blast
	have "B \<noteq> E" using betweennotequal[OF `axioms` `bet A B E`] by blast
	have "E \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> E`] .
	have "b \<noteq> m" using betweennotequal[OF `axioms` `bet b m c`] by blast
	obtain Q where "bet E B Q \<and> seg_eq B Q b m" using extensionE[OF `axioms` `E \<noteq> B` `b \<noteq> m`] by blast
	have "bet E B Q" using `bet E B Q \<and> seg_eq B Q b m` by blast
	have "seg_eq B Q b m" using `bet E B Q \<and> seg_eq B Q b m` by blast
	have "seg_eq b m m c" using congruenceflip[OF `axioms` `seg_eq m b m c`] by blast
	have "seg_eq B Q m c" using congruencetransitive[OF `axioms` `seg_eq B Q b m` `seg_eq b m m c`] .
	have "seg_eq m c B E" using congruencesymmetric[OF `axioms` `seg_eq B E m c`] .
	have "seg_eq B Q B E" using congruencetransitive[OF `axioms` `seg_eq B Q m c` `seg_eq m c B E`] .
	have "bet Q B E" using betweennesssymmetryE[OF `axioms` `bet E B Q`] .
	have "seg_eq Q B B E" using congruenceflip[OF `axioms` `seg_eq B Q B E`] by blast
	have "midpoint Q B E" using midpoint_b[OF `axioms` `bet Q B E` `seg_eq Q B B E`] .
	have "\<not> col A B R" using `\<not> col A B R` .
	have "\<not> col B A R" using NCorder[OF `axioms` `\<not> col A B R`] by blast
	have "col A B E" using collinear_b `axioms` `bet A B E \<and> seg_eq B E m c` by blast
	have "col B A E" using collinearorder[OF `axioms` `col A B E`] by blast
	have "B \<noteq> E" using betweennotequal[OF `axioms` `bet A B E`] by blast
	have "\<not> col B E R" using NChelper[OF `axioms` `\<not> col B A R` `col B A B` `col B A E` `B \<noteq> E`] .
	have "\<not> col R B E" using NCorder[OF `axioms` `\<not> col B E R`] by blast
	obtain F G where "parallelogram G B E F \<and> qua_eq_area a b m c G B E F \<and> ang_eq E B G J D N \<and> same_side R G B E" using Prop42B[OF `axioms` `triangle a b c` `midpoint b m c` `\<not> col J D N` `midpoint Q B E` `seg_eq B E m c` `\<not> col R B E`]  by  blast
	have "parallelogram G B E F" using `parallelogram G B E F \<and> qua_eq_area a b m c G B E F \<and> ang_eq E B G J D N \<and> same_side R G B E` by blast
	have "parallelogram B E F G" using PGrotate[OF `axioms` `parallelogram G B E F`] .
	have "qua_eq_area a b m c G B E F" using `parallelogram G B E F \<and> qua_eq_area a b m c G B E F \<and> ang_eq E B G J D N \<and> same_side R G B E` by blast
	have "ang_eq E B G J D N" using `parallelogram G B E F \<and> qua_eq_area a b m c G B E F \<and> ang_eq E B G J D N \<and> same_side R G B E` by blast
	have "same_side R G B E" using `parallelogram G B E F \<and> qua_eq_area a b m c G B E F \<and> ang_eq E B G J D N \<and> same_side R G B E` by blast
	obtain L M where "parallelogram A B M L \<and> ang_eq A B M J D N \<and> qua_eq_area B E F G L M B A \<and> bet G B M" using Prop44A[OF `axioms` `parallelogram B E F G` `ang_eq E B G J D N` `bet A B E`]  by  blast
	have "parallelogram A B M L" using `parallelogram A B M L \<and> ang_eq A B M J D N \<and> qua_eq_area B E F G L M B A \<and> bet G B M` by blast
	have "ang_eq A B M J D N" using `parallelogram A B M L \<and> ang_eq A B M J D N \<and> qua_eq_area B E F G L M B A \<and> bet G B M` by blast
	have "qua_eq_area B E F G L M B A" using `parallelogram A B M L \<and> ang_eq A B M J D N \<and> qua_eq_area B E F G L M B A \<and> bet G B M` by blast
	have "bet G B M" using `parallelogram A B M L \<and> ang_eq A B M J D N \<and> qua_eq_area B E F G L M B A \<and> bet G B M` by blast
	have "B = B" using equalityreflexiveE[OF `axioms`] .
	have "col A B B" using collinear_b `axioms` `B = B` by blast
	have "parallel G B E F" using parallelogram_f[OF `axioms` `parallelogram G B E F`] by blast
	have "\<not> col G B E" using parallelNC[OF `axioms` `parallel G B E F`] by blast
	have "\<not> col E B G" using NCorder[OF `axioms` `\<not> col G B E`] by blast
	have "col E B A" using collinearorder[OF `axioms` `col A B E`] by blast
	have "B = B" using equalityreflexiveE[OF `axioms`] .
	have "col E B B" using collinear_b `axioms` `B = B` by blast
	have "\<not> col A B G" using NChelper[OF `axioms` `\<not> col E B G` `col E B A` `col E B B` `A \<noteq> B`] .
	have "oppo_side G A B M" using oppositeside_b[OF `axioms` `bet G B M` `col A B B` `\<not> col A B G`] .
	have "qua_eq_area a b m c B E F G" using EFpermutationE[OF `axioms` `qua_eq_area a b m c G B E F`] by blast
	have "qua_eq_area a b m c L M B A" using EFtransitiveE[OF `axioms` `qua_eq_area a b m c B E F G` `qua_eq_area B E F G L M B A`] .
	have "qua_eq_area a b m c A B M L" using EFpermutationE[OF `axioms` `qua_eq_area a b m c L M B A`] by blast
	have "col B E A" using collinearorder[OF `axioms` `col A B E`] by blast
	have "same_side R G B A" using samesidecollinear[OF `axioms` `same_side R G B E` `col B E A` `B \<noteq> A`] .
	have "same_side R G A B" using samesideflip[OF `axioms` `same_side R G B A`] .
	have "oppo_side R A B M" using planeseparation[OF `axioms` `same_side R G A B` `oppo_side G A B M`] .
	have "oppo_side M A B R" using oppositesidesymmetric[OF `axioms` `oppo_side R A B M`] .
	have "parallelogram A B M L \<and> ang_eq A B M J D N \<and> qua_eq_area a b m c A B M L \<and> midpoint b m c \<and> oppo_side M A B R" using `parallelogram A B M L \<and> ang_eq A B M J D N \<and> qua_eq_area B E F G L M B A \<and> bet G B M` `parallelogram A B M L \<and> ang_eq A B M J D N \<and> qua_eq_area B E F G L M B A \<and> bet G B M` `qua_eq_area a b m c A B M L` `midpoint b m c` `oppo_side M A B R` by blast
	thus ?thesis by blast
qed

end