theory Playfairhelper
	imports Axioms Definitions Theorems
begin

theorem Playfairhelper:
	assumes: `axioms`
		"parallel A B C D"
		"parallel A B C E"
		"cross A D B C"
		"cross A E B C"
	shows: "col C D E"
proof -
	obtain M where "bet A M D \<and> bet B M C" sorry
	obtain m where "bet A m E \<and> bet B m C" sorry
	have "bet A M D" using `bet A M D \<and> bet B M C` by blast
	have "bet B M C" using `bet A M D \<and> bet B M C` by blast
	have "bet A m E" using `bet A m E \<and> bet B m C` by blast
	have "bet B m C" using `bet A m E \<and> bet B m C` by blast
	have "B \<noteq> C" using betweennotequal[OF `axioms` `bet B M C`] by blast
	have "bet E m A" using betweennesssymmetryE[OF `axioms` `bet A m E`] .
	have "bet D M A" using betweennesssymmetryE[OF `axioms` `bet A M D`] .
	have "col B M C" using col_b `axioms` `bet A M D \<and> bet B M C` by blast
	have "col B m C" using col_b `axioms` `bet A m E \<and> bet B m C` by blast
	have "col C B M" using collinearorder[OF `axioms` `col B M C`] by blast
	have "col C B m" using collinearorder[OF `axioms` `col B m C`] by blast
	have "\<not> col B C E" using parallelNC[OF `axioms` `parallel A B C E`] by blast
	have "\<not> col C B E" using NCorder[OF `axioms` `\<not> col B C E`] by blast
	have "\<not> col B C D" using parallelNC[OF `axioms` `parallel A B C D`] by blast
	have "\<not> col C B D" using NCorder[OF `axioms` `\<not> col B C D`] by blast
	have "oppo_side E C B A" sorry
	have "oppo_side D C B A" sorry
	have "parallel C D A B" using parallelsymmetric[OF `axioms` `parallel A B C D`] .
	have "parallel C E A B" using parallelsymmetric[OF `axioms` `parallel A B C E`] .
	have "parallel E C B A" using parallelflip[OF `axioms` `parallel C E A B`] by blast
	have "parallel D C B A" using parallelflip[OF `axioms` `parallel C D A B`] by blast
	have "ang_eq E C B C B A" using Prop29B[OF `axioms` `parallel E C B A` `oppo_side E C B A`] .
	have "ang_eq D C B C B A" using Prop29B[OF `axioms` `parallel D C B A` `oppo_side D C B A`] .
	have "ang_eq C B A D C B" using equalanglessymmetric[OF `axioms` `ang_eq D C B C B A`] .
	have "ang_eq E C B D C B" using equalanglestransitive[OF `axioms` `ang_eq E C B C B A` `ang_eq C B A D C B`] .
	have "C \<noteq> E" using NCdistinct[OF `axioms` `\<not> col B C E`] by blast
	have "C \<noteq> D" using NCdistinct[OF `axioms` `\<not> col B C D`] by blast
	obtain e where "ray_on C E e \<and> seg_eq C e C D" using layoff[OF `axioms` `C \<noteq> E` `C \<noteq> D`]  by  blast
	have "ray_on C E e" using `ray_on C E e \<and> seg_eq C e C D` by blast
	have "seg_eq C e C D" using `ray_on C E e \<and> seg_eq C e C D` by blast
	have "B = B" using equalityreflexiveE[OF `axioms`] .
	have "C \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> C`] .
	have "ray_on C B B" using ray4 `axioms` `B = B` `C \<noteq> B` by blast
	have "seg_eq C B C B" using congruencereflexiveE[OF `axioms`] .
	have "\<not> col E C B" using NCorder[OF `axioms` `\<not> col B C E`] by blast
	have "ang_eq E C B E C B" using equalanglesreflexive[OF `axioms` `\<not> col E C B`] .
	have "ang_eq E C B e C B" using equalangleshelper[OF `axioms` `ang_eq E C B E C B` `ray_on C E e` `ray_on C B B`] .
	have "ang_eq e C B E C B" using equalanglessymmetric[OF `axioms` `ang_eq E C B e C B`] .
	have "ang_eq e C B D C B" using equalanglestransitive[OF `axioms` `ang_eq e C B E C B` `ang_eq E C B D C B`] .
	have "col C E e" using rayimpliescollinear[OF `axioms` `ray_on C E e`] .
	have "C = C" using equalityreflexiveE[OF `axioms`] .
	have "col C E C" using col_b `axioms` `C = C` by blast
	have "\<not> col C E B" using NCorder[OF `axioms` `\<not> col B C E`] by blast
	have "C \<noteq> e" using raystrict[OF `axioms` `ray_on C E e`] .
	have "\<not> col C e B" using NChelper[OF `axioms` `\<not> col C E B` `col C E C` `col C E e` `C \<noteq> e`] .
	have "\<not> col e C B" using NCorder[OF `axioms` `\<not> col C e B`] by blast
	have "seg_eq e B D B" using Prop04[OF `axioms` `seg_eq C e C D` `seg_eq C B C B` `ang_eq e C B D C B`] by blast
	have "\<not> col B C E" using parallelNC[OF `axioms` `parallel A B C E`] by blast
	have "\<not> col C B E" using NCorder[OF `axioms` `\<not> col B C E`] by blast
	have "\<not> col B C D" using parallelNC[OF `axioms` `parallel A B C D`] by blast
	have "\<not> col C B D" using NCorder[OF `axioms` `\<not> col B C D`] by blast
	have "col C B m \<and> col C B M \<and> bet E m A \<and> bet D M A \<and> \<not> col C B E \<and> \<not> col C B E" using `col C B m` `col C B M` `bet E m A` `bet D M A` `\<not> col C B E` `\<not> col C B E` by blast
	have "same_side E D C B" sorry
	have "\<not> col C B e" using NCorder[OF `axioms` `\<not> col C e B`] by blast
	have "col C C B" using col_b `axioms` `C = C` by blast
	have "ray_on C e E" using ray5[OF `axioms` `ray_on C E e`] .
	have "same_side e e C B" using samesidereflexive[OF `axioms` `\<not> col C B e`] .
	have "same_side e E C B" using sameside2[OF `axioms` `same_side e e C B` `col C C B` `ray_on C e E`] .
	have "same_side e D C B" using samesidetransitive[OF `axioms` `same_side e E C B` `same_side E D C B`] .
	have "seg_eq e C D C" using congruenceflip[OF `axioms` `seg_eq C e C D`] by blast
	have "seg_eq e B D B" using `seg_eq e B D B` .
	have "e = D" using Prop07[OF `axioms` `C \<noteq> B` `seg_eq e C D C` `seg_eq e B D B` `same_side e D C B`] .
	have "col C E D" sorry
	have "col C D E" using collinearorder[OF `axioms` `col C E D`] by blast
	thus ?thesis by blast
qed

end