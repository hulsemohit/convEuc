theory squareparallelogram
	imports n8_2 Euclid4 Geometry NCdistinct NChelper NCorder Prop04 Prop46 betweennesspreserved betweennotequal collinear4 collinearorder collinearright congruenceflip congruencesymmetric congruencetransitive diagonalsbisect equalangleshelper equalanglessymmetric layoffunique oppositesideflip ray4 rightangleNC righttogether
begin

theorem squareparallelogram:
	assumes "axioms"
		"square A B C D"
	shows "parallelogram A B C D"
proof -
	have "seg_eq A B C D \<and> seg_eq A B B C \<and> seg_eq A B D A \<and> ang_right D A B \<and> ang_right A B C \<and> ang_right B C D \<and> ang_right C D A" using square_f[OF `axioms` `square A B C D`] .
	have "seg_eq A B D A" using `seg_eq A B C D \<and> seg_eq A B B C \<and> seg_eq A B D A \<and> ang_right D A B \<and> ang_right A B C \<and> ang_right B C D \<and> ang_right C D A` by blast
	have "ang_right D A B" using `seg_eq A B C D \<and> seg_eq A B B C \<and> seg_eq A B D A \<and> ang_right D A B \<and> ang_right A B C \<and> ang_right B C D \<and> ang_right C D A` by blast
	have "ang_right C D A" using `seg_eq A B C D \<and> seg_eq A B B C \<and> seg_eq A B D A \<and> ang_right D A B \<and> ang_right A B C \<and> ang_right B C D \<and> ang_right C D A` by blast
	have "\<not> col D A B" using rightangleNC[OF `axioms` `ang_right D A B`] .
	have "D \<noteq> A" using NCdistinct[OF `axioms` `\<not> col D A B`] by blast
	obtain R where "bet D A R \<and> seg_eq A R D A" using extensionE[OF `axioms` `D \<noteq> A` `D \<noteq> A`]  by  blast
	have "bet D A R" using `bet D A R \<and> seg_eq A R D A` by blast
	have "bet R A D" using betweennesssymmetryE[OF `axioms` `bet D A R`] .
	have "A \<noteq> B" using NCdistinct[OF `axioms` `\<not> col D A B`] by blast
	have "col D A R" using collinear_b `axioms` `bet D A R \<and> seg_eq A R D A` by blast
	have "A = A" using equalityreflexiveE[OF `axioms`] .
	have "col D A A" using collinear_b `axioms` `A = A` by blast
	have "R \<noteq> A" using betweennotequal[OF `axioms` `bet R A D`] by blast
	have "\<not> col R A B" using NChelper[OF `axioms` `\<not> col D A B` `col D A R` `col D A A` `R \<noteq> A`] .
	have "\<not> col A B R" using NCorder[OF `axioms` `\<not> col R A B`] by blast
	obtain E c where "square A B c E \<and> oppo_side E A B R \<and> parallelogram A B c E" using Prop46[OF `axioms` `A \<noteq> B` `\<not> col A B R`]  by  blast
	have "square A B c E" using `square A B c E \<and> oppo_side E A B R \<and> parallelogram A B c E` by blast
	have "oppo_side E A B R" using `square A B c E \<and> oppo_side E A B R \<and> parallelogram A B c E` by blast
	have "parallelogram A B c E" using `square A B c E \<and> oppo_side E A B R \<and> parallelogram A B c E` by blast
	have "seg_eq A B c E \<and> seg_eq A B B c \<and> seg_eq A B E A \<and> ang_right E A B \<and> ang_right A B c \<and> ang_right B c E \<and> ang_right c E A" using square_f[OF `axioms` `square A B c E`] .
	have "ang_right E A B" using `seg_eq A B c E \<and> seg_eq A B B c \<and> seg_eq A B E A \<and> ang_right E A B \<and> ang_right A B c \<and> ang_right B c E \<and> ang_right c E A` by blast
	have "ang_right c E A" using `seg_eq A B c E \<and> seg_eq A B B c \<and> seg_eq A B E A \<and> ang_right E A B \<and> ang_right A B c \<and> ang_right B c E \<and> ang_right c E A` by blast
	have "ang_right D A B" using `ang_right D A B` .
	have "col R A D" using collinear_b `axioms` `bet R A D` by blast
	have "col D A R" using collinearorder[OF `axioms` `col R A D`] by blast
	have "ang_right R A B" using collinearright[OF `axioms` `ang_right D A B` `col D A R` `R \<noteq> A`] .
	have "ang_right B A R" using n8_2[OF `axioms` `ang_right R A B`] .
	have "oppo_side E B A R" using oppositesideflip[OF `axioms` `oppo_side E A B R`] .
	have "bet E A R" using righttogether[OF `axioms` `ang_right E A B` `ang_right B A R` `oppo_side E B A R`] by blast
	have "bet R A E" using betweennesssymmetryE[OF `axioms` `bet E A R`] .
	have "ray_on A D E" using ray_b[OF `axioms` `bet R A E` `bet R A D`] .
	have "seg_eq A B E A" using square_f[OF `axioms` `square A B c E`] by blast
	have "seg_eq E A A B" using congruencesymmetric[OF `axioms` `seg_eq A B E A`] .
	have "seg_eq E A D A" using congruencetransitive[OF `axioms` `seg_eq E A A B` `seg_eq A B D A`] .
	have "seg_eq A E A D" using congruenceflip[OF `axioms` `seg_eq E A D A`] by blast
	have "A \<noteq> D" using betweennotequal[OF `axioms` `bet R A D`] by blast
	have "D = D" using equalityreflexiveE[OF `axioms`] .
	have "ray_on A D D" using ray4 `axioms` `D = D` `A \<noteq> D` by blast
	have "E = D" using layoffunique[OF `axioms` `ray_on A D E` `ray_on A D D` `seg_eq A E A D`] .
	have "parallelogram A B c D" using `parallelogram A B c E` `E = D` by blast
	have "seg_eq A B C D" using square_f[OF `axioms` `square A B C D`] by blast
	have "square A B c D" using `square A B c E` `E = D` by blast
	have "seg_eq A B c D" using square_f[OF `axioms` `square A B c D`] by blast
	have "seg_eq c D A B" using congruencesymmetric[OF `axioms` `seg_eq A B c D`] .
	have "seg_eq c D C D" using congruencetransitive[OF `axioms` `seg_eq c D A B` `seg_eq A B C D`] .
	have "seg_eq A B B C" using square_f[OF `axioms` `square A B C D`] by blast
	have "seg_eq A B B c" using square_f[OF `axioms` `square A B c D`] by blast
	have "seg_eq B c A B" using congruencesymmetric[OF `axioms` `seg_eq A B B c`] .
	have "seg_eq B c B C" using congruencetransitive[OF `axioms` `seg_eq B c A B` `seg_eq A B B C`] .
	have "seg_eq c B C B" using congruenceflip[OF `axioms` `seg_eq B c B C`] by blast
	have "ang_right B C D" using square_f[OF `axioms` `square A B C D`] by blast
	have "ang_right B c D" using square_f[OF `axioms` `square A B c D`] by blast
	have "ang_eq B c D B C D" using Euclid4[OF `axioms` `ang_right B c D` `ang_right B C D`] .
	have "seg_eq B D B D \<and> ang_eq c B D C B D \<and> ang_eq c D B C D B" using Prop04[OF `axioms` `seg_eq c B C B` `seg_eq c D C D` `ang_eq B c D B C D`] .
	have "ang_eq c D B C D B" using `seg_eq B D B D \<and> ang_eq c B D C B D \<and> ang_eq c D B C D B` by blast
	obtain m where "midpoint A m c \<and> midpoint B m D" using diagonalsbisect[OF `axioms` `parallelogram A B c D`]  by  blast
	have "midpoint A m c" using `midpoint A m c \<and> midpoint B m D` by blast
	have "midpoint B m D" using `midpoint A m c \<and> midpoint B m D` by blast
	have "bet A m c \<and> seg_eq A m m c" using midpoint_f[OF `axioms` `midpoint A m c`] .
	have "bet B m D \<and> seg_eq B m m D" using midpoint_f[OF `axioms` `midpoint B m D`] .
	have "bet A m c" using `bet A m c \<and> seg_eq A m m c` by blast
	have "bet B m D" using `bet B m D \<and> seg_eq B m m D` by blast
	have "seg_eq c D C D" using `seg_eq c D C D` .
	have "ang_eq C D B c D B" using equalanglessymmetric[OF `axioms` `ang_eq c D B C D B`] .
	have "seg_eq D m D m" using congruencereflexiveE[OF `axioms`] .
	have "seg_eq D c D C" using congruenceflip[OF `axioms` `seg_eq c D C D`] by blast
	have "\<not> col C D A" using rightangleNC[OF `axioms` `ang_right C D A`] .
	have "ang_right c D A" using `ang_right c E A` `E = D` by blast
	have "\<not> col c D A" using rightangleNC[OF `axioms` `ang_right c D A`] .
	have "\<not> col A c D" using NCorder[OF `axioms` `\<not> col c D A`] by blast
	have "c = c" using equalityreflexiveE[OF `axioms`] .
	have "col A c c" using collinear_b `axioms` `c = c` by blast
	have "col A m c" using collinear_b `axioms` `bet A m c \<and> seg_eq A m m c` by blast
	have "col A c m" using collinearorder[OF `axioms` `col A m c`] by blast
	have "m \<noteq> c" using betweennotequal[OF `axioms` `bet A m c`] by blast
	have "\<not> col m c D" using NChelper[OF `axioms` `\<not> col A c D` `col A c m` `col A c c` `m \<noteq> c`] .
	have "\<not> col c D m" using NCorder[OF `axioms` `\<not> col m c D`] by blast
	have "\<not> (col C D m)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col C D m))"
hence "col C D m" by blast
		have "col B m D" using collinear_b `axioms` `bet B m D \<and> seg_eq B m m D` by blast
		have "col m D B" using collinearorder[OF `axioms` `col B m D`] by blast
		have "col m D C" using collinearorder[OF `axioms` `col C D m`] by blast
		have "m \<noteq> D" using betweennotequal[OF `axioms` `bet B m D`] by blast
		have "col D B C" using collinear4[OF `axioms` `col m D B` `col m D C` `m \<noteq> D`] .
		have "col B C D" using collinearorder[OF `axioms` `col D B C`] by blast
		have "\<not> col B C D" using rightangleNC[OF `axioms` `ang_right B C D`] .
		show "False" using `\<not> col B C D` `col B C D` by blast
	qed
	hence "\<not> col C D m" by blast
	have "seg_eq D c D C" using `seg_eq D c D C` .
	have "ang_eq c D B C D B" using equalanglessymmetric[OF `axioms` `ang_eq C D B c D B`] .
	have "bet D m B" using betweennesssymmetryE[OF `axioms` `bet B m D`] .
	have "D \<noteq> B" using betweennotequal[OF `axioms` `bet D m B`] by blast
	have "ray_on D B m" using ray4 `axioms` `bet D m B` `D \<noteq> B` by blast
	have "C = C" using equalityreflexiveE[OF `axioms`] .
	have "D \<noteq> C" using NCdistinct[OF `axioms` `\<not> col C D A`] by blast
	have "ray_on D C C" using ray4 `axioms` `C = C` `D \<noteq> C` by blast
	have "ang_eq c D B C D m" using equalangleshelper[OF `axioms` `ang_eq c D B C D B` `ray_on D C C` `ray_on D B m`] .
	have "ang_eq C D m c D B" using equalanglessymmetric[OF `axioms` `ang_eq c D B C D m`] .
	have "c = c" using equalityreflexiveE[OF `axioms`] .
	have "D \<noteq> c" using NCdistinct[OF `axioms` `\<not> col A c D`] by blast
	have "ray_on D c c" using ray4 `axioms` `c = c` `D \<noteq> c` by blast
	have "ang_eq C D m c D m" using equalangleshelper[OF `axioms` `ang_eq C D m c D B` `ray_on D c c` `ray_on D B m`] .
	have "ang_eq c D m C D m" using equalanglessymmetric[OF `axioms` `ang_eq C D m c D m`] .
	have "seg_eq c m C m" using Prop04[OF `axioms` `seg_eq D c D C` `seg_eq D m D m` `ang_eq c D m C D m`] by blast
	have "seg_eq m c m C" using congruenceflip[OF `axioms` `seg_eq c m C m`] by blast
	have "seg_eq A m A m" using congruencereflexiveE[OF `axioms`] .
	have "seg_eq D A D A" using congruencereflexiveE[OF `axioms`] .
	have "ang_right c D A" using `ang_right c D A` by blast
	have "ang_right A D c" using n8_2[OF `axioms` `ang_right c D A`] .
	have "ang_right A D C" using n8_2[OF `axioms` `ang_right C D A`] .
	have "ang_eq A D C A D c" using Euclid4[OF `axioms` `ang_right A D C` `ang_right A D c`] .
	have "seg_eq D C D c" using congruencesymmetric[OF `axioms` `seg_eq D c D C`] .
	have "seg_eq A C A c" using Prop04[OF `axioms` `seg_eq D A D A` `seg_eq D C D c` `ang_eq A D C A D c`] by blast
	have "seg_eq A c A C" using congruencesymmetric[OF `axioms` `seg_eq A C A c`] .
	have "bet A m c" using `bet A m c` .
	have "bet A m C" using betweennesspreserved[OF `axioms` `seg_eq A m A m` `seg_eq A c A C` `seg_eq m c m C` `bet A m c`] .
	have "A \<noteq> m" using betweennotequal[OF `axioms` `bet A m C`] by blast
	have "ray_on A m c" using ray4 `axioms` `bet A m c \<and> seg_eq A m m c` `A \<noteq> m` by blast
	have "ray_on A m C" using ray4 `axioms` `bet A m C` `A \<noteq> m` by blast
	have "c = C" using layoffunique[OF `axioms` `ray_on A m c` `ray_on A m C` `seg_eq A c A C`] .
	have "parallelogram A B C D" using `parallelogram A B c D` `c = C` by blast
	thus ?thesis by blast
qed

end