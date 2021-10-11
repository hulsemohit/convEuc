theory Prop14
	imports Geometry NCdistinct NChelper NCorder Prop04 Prop07 betweennotequal collinearorder congruenceflip equalanglesNC equalanglessymmetric equalanglestransitive inequalitysymmetric oppositesidesymmetric rayimpliescollinear supplements
begin

theorem(in euclidean_geometry) Prop14:
	assumes 
		"ang_sum_right A B C D B E"
		"ray_on B C D"
		"oppo_side E D B A"
	shows "supplement A B C D E \<and> bet A B E"
proof -
	obtain a b c d e where "supplement a b c d e \<and> ang_eq A B C a b c \<and> ang_eq D B E d b e" using tworightangles_f[OF `ang_sum_right A B C D B E`]  by  blast
	have "supplement a b c d e" using `supplement a b c d e \<and> ang_eq A B C a b c \<and> ang_eq D B E d b e` by blast
	have "ang_eq A B C a b c" using `supplement a b c d e \<and> ang_eq A B C a b c \<and> ang_eq D B E d b e` by blast
	have "ang_eq D B E d b e" using `supplement a b c d e \<and> ang_eq A B C a b c \<and> ang_eq D B E d b e` by blast
	have "ang_eq a b c A B C" using equalanglessymmetric[OF `ang_eq A B C a b c`] .
	have "ang_eq d b e D B E" using equalanglessymmetric[OF `ang_eq D B E d b e`] .
	have "\<not> col A B C" using equalanglesNC[OF `ang_eq a b c A B C`] .
	have "A \<noteq> B" using NCdistinct[OF `\<not> col A B C`] by blast
	have "\<not> col D B E" using equalanglesNC[OF `ang_eq d b e D B E`] .
	have "B \<noteq> E" using NCdistinct[OF `\<not> col D B E`] by blast
	obtain T where "bet A B T \<and> seg_eq B T B E" using extensionE[OF `A \<noteq> B` `B \<noteq> E`]  by  blast
	have "bet A B T" using `bet A B T \<and> seg_eq B T B E` by blast
	have "seg_eq B T B E" using `bet A B T \<and> seg_eq B T B E` by blast
	have "seg_eq B D B D" using congruencereflexiveE.
	have "ang_eq D B E d b e" using `ang_eq D B E d b e` .
	have "ang_eq A B C a b c" using `ang_eq A B C a b c` .
	have "supplement A B C D T" using supplement_b[OF `ray_on B C D` `bet A B T`] .
	have "ang_eq a b c A B C" using equalanglessymmetric[OF `ang_eq A B C a b c`] .
	have "ang_eq d b e D B E" using equalanglessymmetric[OF `ang_eq D B E d b e`] .
	have "ang_eq d b e D B T" using supplements[OF `ang_eq a b c A B C` `supplement a b c d e` `supplement A B C D T`] .
	have "ang_eq D B E D B T" using equalanglestransitive[OF `ang_eq D B E d b e` `ang_eq d b e D B T`] .
	have "ang_eq D B T D B E" using equalanglessymmetric[OF `ang_eq D B E D B T`] .
	have "col A B T" using collinear_b `bet A B T \<and> seg_eq B T B E` by blast
	have "B \<noteq> T" using betweennotequal[OF `bet A B T`] by blast
	have "T \<noteq> B" using inequalitysymmetric[OF `B \<noteq> T`] .
	have "B = B" using equalityreflexiveE.
	have "col A B B" using collinear_b `B = B` by blast
	have "\<not> col T B C" using NChelper[OF `\<not> col A B C` `col A B T` `col A B B` `T \<noteq> B`] .
	have "\<not> col C B T" using NCorder[OF `\<not> col T B C`] by blast
	have "col B C D" using rayimpliescollinear[OF `ray_on B C D`] .
	have "col C B D" using collinearorder[OF `col B C D`] by blast
	have "D \<noteq> B" using NCdistinct[OF `\<not> col D B E`] by blast
	have "col C B B" using collinear_b `B = B` by blast
	have "\<not> col D B T" using NChelper[OF `\<not> col C B T` `col C B D` `col C B B` `D \<noteq> B`] .
	have "seg_eq D T D E" using Prop04[OF `seg_eq B D B D` `seg_eq B T B E` `ang_eq D B T D B E`] by blast
	have "seg_eq T D E D" using congruenceflip[OF `seg_eq D T D E`] by blast
	have "seg_eq T B E B" using congruenceflip[OF `seg_eq B T B E`] by blast
	have "col D B B" using collinear_b `B = B` by blast
	have "oppo_side A D B E" using oppositesidesymmetric[OF `oppo_side E D B A`] .
	obtain m where "bet A m E \<and> col D B m \<and> \<not> col D B A" using oppositeside_f[OF `oppo_side A D B E`]  by  blast
	have "bet A m E" using `bet A m E \<and> col D B m \<and> \<not> col D B A` by blast
	have "col D B m" using `bet A m E \<and> col D B m \<and> \<not> col D B A` by blast
	have "\<not> col D B E" using `\<not> col D B E` .
	have "bet E m A" using betweennesssymmetryE[OF `bet A m E`] .
	have "bet T B A" using betweennesssymmetryE[OF `bet A B T`] .
	have "col D B B \<and> col D B m \<and> bet T B A \<and> bet E m A \<and> \<not> col D B T \<and> \<not> col D B E" using `col D B B` `bet A m E \<and> col D B m \<and> \<not> col D B A` `bet T B A` `bet E m A` `\<not> col D B T` `\<not> col D B E` by blast
	have "same_side T E D B" using sameside_b[OF `col D B B` `col D B m` `bet T B A` `bet E m A` `\<not> col D B T` `\<not> col D B E`] .
	have "B \<noteq> C" using NCdistinct[OF `\<not> col A B C`] by blast
	have "C \<noteq> B" using inequalitysymmetric[OF `B \<noteq> C`] .
	have "T = E" using Prop07[OF `D \<noteq> B` `seg_eq T D E D` `seg_eq T B E B` `same_side T E D B`] .
	have "bet A B E" using `bet A B T` `T = E` by blast
	have "supplement A B C D E" using supplement_b[OF `ray_on B C D` `bet A B E`] .
	have "supplement A B C D E \<and> bet A B E" using `supplement A B C D E` `bet A B E` by blast
	thus ?thesis by blast
qed

end