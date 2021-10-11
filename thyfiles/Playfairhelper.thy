theory Playfairhelper
	imports Geometry NCdistinct NChelper NCorder Prop04 Prop07 Prop29B betweennotequal collinearorder congruenceflip equalangleshelper equalanglesreflexive equalanglessymmetric equalanglestransitive inequalitysymmetric layoff parallelNC parallelflip parallelsymmetric ray4 ray5 rayimpliescollinear raystrict sameside2 samesidereflexive samesidetransitive
begin

theorem(in euclidean_geometry) Playfairhelper:
	assumes 
		"parallel A B C D"
		"parallel A B C E"
		"cross A D B C"
		"cross A E B C"
	shows "col C D E"
proof -
	obtain M where "bet A M D \<and> bet B M C" using cross_f[OF `cross A D B C`]  by  blast
	obtain m where "bet A m E \<and> bet B m C" using cross_f[OF `cross A E B C`]  by  blast
	have "bet A M D" using `bet A M D \<and> bet B M C` by blast
	have "bet B M C" using `bet A M D \<and> bet B M C` by blast
	have "bet A m E" using `bet A m E \<and> bet B m C` by blast
	have "bet B m C" using `bet A m E \<and> bet B m C` by blast
	have "B \<noteq> C" using betweennotequal[OF `bet B M C`] by blast
	have "bet E m A" using betweennesssymmetryE[OF `bet A m E`] .
	have "bet D M A" using betweennesssymmetryE[OF `bet A M D`] .
	have "col B M C" using collinear_b `bet A M D \<and> bet B M C` by blast
	have "col B m C" using collinear_b `bet A m E \<and> bet B m C` by blast
	have "col C B M" using collinearorder[OF `col B M C`] by blast
	have "col C B m" using collinearorder[OF `col B m C`] by blast
	have "\<not> col B C E" using parallelNC[OF `parallel A B C E`] by blast
	have "\<not> col C B E" using NCorder[OF `\<not> col B C E`] by blast
	have "\<not> col B C D" using parallelNC[OF `parallel A B C D`] by blast
	have "\<not> col C B D" using NCorder[OF `\<not> col B C D`] by blast
	have "oppo_side E C B A" using oppositeside_b[OF `bet E m A` `col C B m` `\<not> col C B E`] .
	have "oppo_side D C B A" using oppositeside_b[OF `bet D M A` `col C B M` `\<not> col C B D`] .
	have "parallel C D A B" using parallelsymmetric[OF `parallel A B C D`] .
	have "parallel C E A B" using parallelsymmetric[OF `parallel A B C E`] .
	have "parallel E C B A" using parallelflip[OF `parallel C E A B`] by blast
	have "parallel D C B A" using parallelflip[OF `parallel C D A B`] by blast
	have "ang_eq E C B C B A" using Prop29B[OF `parallel E C B A` `oppo_side E C B A`] .
	have "ang_eq D C B C B A" using Prop29B[OF `parallel D C B A` `oppo_side D C B A`] .
	have "ang_eq C B A D C B" using equalanglessymmetric[OF `ang_eq D C B C B A`] .
	have "ang_eq E C B D C B" using equalanglestransitive[OF `ang_eq E C B C B A` `ang_eq C B A D C B`] .
	have "C \<noteq> E" using NCdistinct[OF `\<not> col B C E`] by blast
	have "C \<noteq> D" using NCdistinct[OF `\<not> col B C D`] by blast
	obtain e where "ray_on C E e \<and> seg_eq C e C D" using layoff[OF `C \<noteq> E` `C \<noteq> D`]  by  blast
	have "ray_on C E e" using `ray_on C E e \<and> seg_eq C e C D` by blast
	have "seg_eq C e C D" using `ray_on C E e \<and> seg_eq C e C D` by blast
	have "B = B" using equalityreflexiveE.
	have "C \<noteq> B" using inequalitysymmetric[OF `B \<noteq> C`] .
	have "ray_on C B B" using ray4 `B = B` `C \<noteq> B` by blast
	have "seg_eq C B C B" using congruencereflexiveE.
	have "\<not> col E C B" using NCorder[OF `\<not> col B C E`] by blast
	have "ang_eq E C B E C B" using equalanglesreflexive[OF `\<not> col E C B`] .
	have "ang_eq E C B e C B" using equalangleshelper[OF `ang_eq E C B E C B` `ray_on C E e` `ray_on C B B`] .
	have "ang_eq e C B E C B" using equalanglessymmetric[OF `ang_eq E C B e C B`] .
	have "ang_eq e C B D C B" using equalanglestransitive[OF `ang_eq e C B E C B` `ang_eq E C B D C B`] .
	have "col C E e" using rayimpliescollinear[OF `ray_on C E e`] .
	have "C = C" using equalityreflexiveE.
	have "col C E C" using collinear_b `C = C` by blast
	have "\<not> col C E B" using NCorder[OF `\<not> col B C E`] by blast
	have "C \<noteq> e" using raystrict[OF `ray_on C E e`] .
	have "\<not> col C e B" using NChelper[OF `\<not> col C E B` `col C E C` `col C E e` `C \<noteq> e`] .
	have "\<not> col e C B" using NCorder[OF `\<not> col C e B`] by blast
	have "seg_eq e B D B" using Prop04[OF `seg_eq C e C D` `seg_eq C B C B` `ang_eq e C B D C B`] by blast
	have "\<not> col B C E" using parallelNC[OF `parallel A B C E`] by blast
	have "\<not> col C B E" using NCorder[OF `\<not> col B C E`] by blast
	have "\<not> col B C D" using parallelNC[OF `parallel A B C D`] by blast
	have "\<not> col C B D" using NCorder[OF `\<not> col B C D`] by blast
	have "col C B m \<and> col C B M \<and> bet E m A \<and> bet D M A \<and> \<not> col C B E \<and> \<not> col C B E" using `col C B m` `col C B M` `bet E m A` `bet D M A` `\<not> col C B E` `\<not> col C B E` by blast
	have "same_side E D C B" using sameside_b[OF `col C B m` `col C B M` `bet E m A` `bet D M A` `\<not> col C B E` `\<not> col C B D`] .
	have "\<not> col C B e" using NCorder[OF `\<not> col C e B`] by blast
	have "col C C B" using collinear_b `C = C` by blast
	have "ray_on C e E" using ray5[OF `ray_on C E e`] .
	have "same_side e e C B" using samesidereflexive[OF `\<not> col C B e`] .
	have "same_side e E C B" using sameside2[OF `same_side e e C B` `col C C B` `ray_on C e E`] .
	have "same_side e D C B" using samesidetransitive[OF `same_side e E C B` `same_side E D C B`] .
	have "seg_eq e C D C" using congruenceflip[OF `seg_eq C e C D`] by blast
	have "seg_eq e B D B" using `seg_eq e B D B` .
	have "e = D" using Prop07[OF `C \<noteq> B` `seg_eq e C D C` `seg_eq e B D B` `same_side e D C B`] .
	have "col C E D" using `col C E e` `e = D` by blast
	have "col C D E" using collinearorder[OF `col C E D`] by blast
	thus ?thesis by blast
qed

end