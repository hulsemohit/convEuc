theory squareparallelogram
	imports n8_2 Euclid4 Geometry NCdistinct NChelper NCorder Prop04 Prop46 betweennesspreserved betweennotequal collinear4 collinearorder collinearright congruenceflip congruencesymmetric congruencetransitive diagonalsbisect equalangleshelper equalanglessymmetric layoffunique oppositesideflip ray4 rightangleNC righttogether
begin

theorem(in euclidean_geometry) squareparallelogram:
	assumes 
		"square A B C D"
	shows "parallelogram A B C D"
proof -
	have "seg_eq A B C D \<and> seg_eq A B B C \<and> seg_eq A B D A \<and> ang_right D A B \<and> ang_right A B C \<and> ang_right B C D \<and> ang_right C D A" using square_f[OF `square A B C D`] .
	have "seg_eq A B D A" using `seg_eq A B C D \<and> seg_eq A B B C \<and> seg_eq A B D A \<and> ang_right D A B \<and> ang_right A B C \<and> ang_right B C D \<and> ang_right C D A` by blast
	have "ang_right D A B" using `seg_eq A B C D \<and> seg_eq A B B C \<and> seg_eq A B D A \<and> ang_right D A B \<and> ang_right A B C \<and> ang_right B C D \<and> ang_right C D A` by blast
	have "ang_right C D A" using `seg_eq A B C D \<and> seg_eq A B B C \<and> seg_eq A B D A \<and> ang_right D A B \<and> ang_right A B C \<and> ang_right B C D \<and> ang_right C D A` by blast
	have "\<not> col D A B" using rightangleNC[OF `ang_right D A B`] .
	have "D \<noteq> A" using NCdistinct[OF `\<not> col D A B`] by blast
	obtain R where "bet D A R \<and> seg_eq A R D A" using extensionE[OF `D \<noteq> A` `D \<noteq> A`]  by  blast
	have "bet D A R" using `bet D A R \<and> seg_eq A R D A` by blast
	have "bet R A D" using betweennesssymmetryE[OF `bet D A R`] .
	have "A \<noteq> B" using NCdistinct[OF `\<not> col D A B`] by blast
	have "col D A R" using collinear_b `bet D A R \<and> seg_eq A R D A` by blast
	have "A = A" using equalityreflexiveE.
	have "col D A A" using collinear_b `A = A` by blast
	have "R \<noteq> A" using betweennotequal[OF `bet R A D`] by blast
	have "\<not> col R A B" using NChelper[OF `\<not> col D A B` `col D A R` `col D A A` `R \<noteq> A`] .
	have "\<not> col A B R" using NCorder[OF `\<not> col R A B`] by blast
	obtain E c where "square A B c E \<and> oppo_side E A B R \<and> parallelogram A B c E" using Prop46[OF `A \<noteq> B` `\<not> col A B R`]  by  blast
	have "square A B c E" using `square A B c E \<and> oppo_side E A B R \<and> parallelogram A B c E` by blast
	have "oppo_side E A B R" using `square A B c E \<and> oppo_side E A B R \<and> parallelogram A B c E` by blast
	have "parallelogram A B c E" using `square A B c E \<and> oppo_side E A B R \<and> parallelogram A B c E` by blast
	have "seg_eq A B c E \<and> seg_eq A B B c \<and> seg_eq A B E A \<and> ang_right E A B \<and> ang_right A B c \<and> ang_right B c E \<and> ang_right c E A" using square_f[OF `square A B c E`] .
	have "ang_right E A B" using `seg_eq A B c E \<and> seg_eq A B B c \<and> seg_eq A B E A \<and> ang_right E A B \<and> ang_right A B c \<and> ang_right B c E \<and> ang_right c E A` by blast
	have "ang_right c E A" using `seg_eq A B c E \<and> seg_eq A B B c \<and> seg_eq A B E A \<and> ang_right E A B \<and> ang_right A B c \<and> ang_right B c E \<and> ang_right c E A` by blast
	have "ang_right D A B" using `ang_right D A B` .
	have "col R A D" using collinear_b `bet R A D` by blast
	have "col D A R" using collinearorder[OF `col R A D`] by blast
	have "ang_right R A B" using collinearright[OF `ang_right D A B` `col D A R` `R \<noteq> A`] .
	have "ang_right B A R" using n8_2[OF `ang_right R A B`] .
	have "oppo_side E B A R" using oppositesideflip[OF `oppo_side E A B R`] .
	have "bet E A R" using righttogether[OF `ang_right E A B` `ang_right B A R` `oppo_side E B A R`] by blast
	have "bet R A E" using betweennesssymmetryE[OF `bet E A R`] .
	have "ray_on A D E" using ray_b[OF `bet R A E` `bet R A D`] .
	have "seg_eq A B E A" using square_f[OF `square A B c E`] by blast
	have "seg_eq E A A B" using congruencesymmetric[OF `seg_eq A B E A`] .
	have "seg_eq E A D A" using congruencetransitive[OF `seg_eq E A A B` `seg_eq A B D A`] .
	have "seg_eq A E A D" using congruenceflip[OF `seg_eq E A D A`] by blast
	have "A \<noteq> D" using betweennotequal[OF `bet R A D`] by blast
	have "D = D" using equalityreflexiveE.
	have "ray_on A D D" using ray4 `D = D` `A \<noteq> D` by blast
	have "E = D" using layoffunique[OF `ray_on A D E` `ray_on A D D` `seg_eq A E A D`] .
	have "parallelogram A B c D" using `parallelogram A B c E` `E = D` by blast
	have "seg_eq A B C D" using square_f[OF `square A B C D`] by blast
	have "square A B c D" using `square A B c E` `E = D` by blast
	have "seg_eq A B c D" using square_f[OF `square A B c D`] by blast
	have "seg_eq c D A B" using congruencesymmetric[OF `seg_eq A B c D`] .
	have "seg_eq c D C D" using congruencetransitive[OF `seg_eq c D A B` `seg_eq A B C D`] .
	have "seg_eq A B B C" using square_f[OF `square A B C D`] by blast
	have "seg_eq A B B c" using square_f[OF `square A B c D`] by blast
	have "seg_eq B c A B" using congruencesymmetric[OF `seg_eq A B B c`] .
	have "seg_eq B c B C" using congruencetransitive[OF `seg_eq B c A B` `seg_eq A B B C`] .
	have "seg_eq c B C B" using congruenceflip[OF `seg_eq B c B C`] by blast
	have "ang_right B C D" using square_f[OF `square A B C D`] by blast
	have "ang_right B c D" using square_f[OF `square A B c D`] by blast
	have "ang_eq B c D B C D" using Euclid4[OF `ang_right B c D` `ang_right B C D`] .
	have "seg_eq B D B D \<and> ang_eq c B D C B D \<and> ang_eq c D B C D B" using Prop04[OF `seg_eq c B C B` `seg_eq c D C D` `ang_eq B c D B C D`] .
	have "ang_eq c D B C D B" using `seg_eq B D B D \<and> ang_eq c B D C B D \<and> ang_eq c D B C D B` by blast
	obtain m where "midpoint A m c \<and> midpoint B m D" using diagonalsbisect[OF `parallelogram A B c D`]  by  blast
	have "midpoint A m c" using `midpoint A m c \<and> midpoint B m D` by blast
	have "midpoint B m D" using `midpoint A m c \<and> midpoint B m D` by blast
	have "bet A m c \<and> seg_eq A m m c" using midpoint_f[OF `midpoint A m c`] .
	have "bet B m D \<and> seg_eq B m m D" using midpoint_f[OF `midpoint B m D`] .
	have "bet A m c" using `bet A m c \<and> seg_eq A m m c` by blast
	have "bet B m D" using `bet B m D \<and> seg_eq B m m D` by blast
	have "seg_eq c D C D" using `seg_eq c D C D` .
	have "ang_eq C D B c D B" using equalanglessymmetric[OF `ang_eq c D B C D B`] .
	have "seg_eq D m D m" using congruencereflexiveE.
	have "seg_eq D c D C" using congruenceflip[OF `seg_eq c D C D`] by blast
	have "\<not> col C D A" using rightangleNC[OF `ang_right C D A`] .
	have "ang_right c D A" using `ang_right c E A` `E = D` by blast
	have "\<not> col c D A" using rightangleNC[OF `ang_right c D A`] .
	have "\<not> col A c D" using NCorder[OF `\<not> col c D A`] by blast
	have "c = c" using equalityreflexiveE.
	have "col A c c" using collinear_b `c = c` by blast
	have "col A m c" using collinear_b `bet A m c \<and> seg_eq A m m c` by blast
	have "col A c m" using collinearorder[OF `col A m c`] by blast
	have "m \<noteq> c" using betweennotequal[OF `bet A m c`] by blast
	have "\<not> col m c D" using NChelper[OF `\<not> col A c D` `col A c m` `col A c c` `m \<noteq> c`] .
	have "\<not> col c D m" using NCorder[OF `\<not> col m c D`] by blast
	have "\<not> (col C D m)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col C D m))"
hence "col C D m" by blast
		have "col B m D" using collinear_b `bet B m D \<and> seg_eq B m m D` by blast
		have "col m D B" using collinearorder[OF `col B m D`] by blast
		have "col m D C" using collinearorder[OF `col C D m`] by blast
		have "m \<noteq> D" using betweennotequal[OF `bet B m D`] by blast
		have "col D B C" using collinear4[OF `col m D B` `col m D C` `m \<noteq> D`] .
		have "col B C D" using collinearorder[OF `col D B C`] by blast
		have "\<not> col B C D" using rightangleNC[OF `ang_right B C D`] .
		show "False" using `\<not> col B C D` `col B C D` by blast
	qed
	hence "\<not> col C D m" by blast
	have "seg_eq D c D C" using `seg_eq D c D C` .
	have "ang_eq c D B C D B" using equalanglessymmetric[OF `ang_eq C D B c D B`] .
	have "bet D m B" using betweennesssymmetryE[OF `bet B m D`] .
	have "D \<noteq> B" using betweennotequal[OF `bet D m B`] by blast
	have "ray_on D B m" using ray4 `bet D m B` `D \<noteq> B` by blast
	have "C = C" using equalityreflexiveE.
	have "D \<noteq> C" using NCdistinct[OF `\<not> col C D A`] by blast
	have "ray_on D C C" using ray4 `C = C` `D \<noteq> C` by blast
	have "ang_eq c D B C D m" using equalangleshelper[OF `ang_eq c D B C D B` `ray_on D C C` `ray_on D B m`] .
	have "ang_eq C D m c D B" using equalanglessymmetric[OF `ang_eq c D B C D m`] .
	have "c = c" using equalityreflexiveE.
	have "D \<noteq> c" using NCdistinct[OF `\<not> col A c D`] by blast
	have "ray_on D c c" using ray4 `c = c` `D \<noteq> c` by blast
	have "ang_eq C D m c D m" using equalangleshelper[OF `ang_eq C D m c D B` `ray_on D c c` `ray_on D B m`] .
	have "ang_eq c D m C D m" using equalanglessymmetric[OF `ang_eq C D m c D m`] .
	have "seg_eq c m C m" using Prop04[OF `seg_eq D c D C` `seg_eq D m D m` `ang_eq c D m C D m`] by blast
	have "seg_eq m c m C" using congruenceflip[OF `seg_eq c m C m`] by blast
	have "seg_eq A m A m" using congruencereflexiveE.
	have "seg_eq D A D A" using congruencereflexiveE.
	have "ang_right c D A" using `ang_right c D A` by blast
	have "ang_right A D c" using n8_2[OF `ang_right c D A`] .
	have "ang_right A D C" using n8_2[OF `ang_right C D A`] .
	have "ang_eq A D C A D c" using Euclid4[OF `ang_right A D C` `ang_right A D c`] .
	have "seg_eq D C D c" using congruencesymmetric[OF `seg_eq D c D C`] .
	have "seg_eq A C A c" using Prop04[OF `seg_eq D A D A` `seg_eq D C D c` `ang_eq A D C A D c`] by blast
	have "seg_eq A c A C" using congruencesymmetric[OF `seg_eq A C A c`] .
	have "bet A m c" using `bet A m c` .
	have "bet A m C" using betweennesspreserved[OF `seg_eq A m A m` `seg_eq A c A C` `seg_eq m c m C` `bet A m c`] .
	have "A \<noteq> m" using betweennotequal[OF `bet A m C`] by blast
	have "ray_on A m c" using ray4 `bet A m c \<and> seg_eq A m m c` `A \<noteq> m` by blast
	have "ray_on A m C" using ray4 `bet A m C` `A \<noteq> m` by blast
	have "c = C" using layoffunique[OF `ray_on A m c` `ray_on A m C` `seg_eq A c A C`] .
	have "parallelogram A B C D" using `parallelogram A B c D` `c = C` by blast
	thus ?thesis by blast
qed

end