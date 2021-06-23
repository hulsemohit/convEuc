theory squareunique
	imports Euclid4 Geometry NCdistinct NCorder Prop04 betweennesspreserved betweennotequal congruenceflip congruencesymmetric congruencetransitive diagonalsbisect equalanglesflip equalangleshelper equalanglesreflexive equalanglessymmetric equalanglestransitive layoff layoffunique ray4 ray5 rightangleNC squareparallelogram
begin

theorem squareunique:
	assumes "axioms"
		"square A B C D"
		"square A B C E"
	shows "E = D"
proof -
	have "parallelogram A B C D" using squareparallelogram[OF `axioms` `square A B C D`] .
	obtain M where "midpoint A M C \<and> midpoint B M D" using diagonalsbisect[OF `axioms` `parallelogram A B C D`]  by  blast
	have "midpoint A M C" using `midpoint A M C \<and> midpoint B M D` by blast
	have "midpoint B M D" using `midpoint A M C \<and> midpoint B M D` by blast
	have "bet B M D" using midpoint_f[OF `axioms` `midpoint B M D`] by blast
	have "bet A M C" using midpoint_f[OF `axioms` `midpoint A M C`] by blast
	have "ang_right D A B" using square_f[OF `axioms` `square A B C D`] by blast
	have "ang_right E A B" using square_f[OF `axioms` `square A B C E`] by blast
	have "\<not> col D A B" using rightangleNC[OF `axioms` `ang_right D A B`] .
	have "\<not> col E A B" using rightangleNC[OF `axioms` `ang_right E A B`] .
	have "seg_eq A B A B" using congruencereflexiveE[OF `axioms`] .
	have "seg_eq A B D A" using square_f[OF `axioms` `square A B C D`] by blast
	have "seg_eq A B E A" using square_f[OF `axioms` `square A B C E`] by blast
	have "seg_eq E A A B" using congruencesymmetric[OF `axioms` `seg_eq A B E A`] .
	have "seg_eq E A D A" using congruencetransitive[OF `axioms` `seg_eq E A A B` `seg_eq A B D A`] .
	have "seg_eq A E A D" using congruenceflip[OF `axioms` `seg_eq E A D A`] by blast
	have "ang_eq E A B D A B" using Euclid4[OF `axioms` `ang_right E A B` `ang_right D A B`] .
	have "seg_eq E B D B \<and> ang_eq A E B A D B \<and> ang_eq A B E A B D" using Prop04[OF `axioms` `seg_eq A E A D` `seg_eq A B A B` `ang_eq E A B D A B`] .
	have "ang_eq A B E A B D" using `seg_eq E B D B \<and> ang_eq A E B A D B \<and> ang_eq A B E A B D` by blast
	have "ang_eq A B D A B E" using equalanglessymmetric[OF `axioms` `ang_eq A B E A B D`] .
	have "B \<noteq> E" using NCdistinct[OF `axioms` `\<not> col E A B`] by blast
	have "B \<noteq> M" using betweennotequal[OF `axioms` `bet B M D`] by blast
	obtain N where "ray_on B E N \<and> seg_eq B N B M" using layoff[OF `axioms` `B \<noteq> E` `B \<noteq> M`]  by  blast
	have "ray_on B E N" using `ray_on B E N \<and> seg_eq B N B M` by blast
	have "seg_eq B N B M" using `ray_on B E N \<and> seg_eq B N B M` by blast
	have "seg_eq B M B N" using congruencesymmetric[OF `axioms` `seg_eq B N B M`] .
	have "A = A" using equalityreflexiveE[OF `axioms`] .
	have "B \<noteq> A" using NCdistinct[OF `axioms` `\<not> col D A B`] by blast
	have "ray_on B A A" using ray4 `axioms` `A = A` `B \<noteq> A` by blast
	have "ray_on B M D" using ray4 `axioms` `bet B M D` `B \<noteq> M` by blast
	have "ray_on B D M" using ray5[OF `axioms` `ray_on B M D`] .
	have "\<not> col A B D" using NCorder[OF `axioms` `\<not> col D A B`] by blast
	have "ang_eq A B D A B D" using equalanglesreflexive[OF `axioms` `\<not> col A B D`] .
	have "ang_eq A B D A B M" using equalangleshelper[OF `axioms` `ang_eq A B D A B D` `ray_on B A A` `ray_on B D M`] .
	have "ang_eq A B M A B D" using equalanglessymmetric[OF `axioms` `ang_eq A B D A B M`] .
	have "ang_eq A B M A B E" using equalanglestransitive[OF `axioms` `ang_eq A B M A B D` `ang_eq A B D A B E`] .
	have "\<not> col A B E" using NCorder[OF `axioms` `\<not> col E A B`] by blast
	have "ang_eq A B E A B E" using equalanglesreflexive[OF `axioms` `\<not> col A B E`] .
	have "ang_eq A B E A B N" using equalangleshelper[OF `axioms` `ang_eq A B E A B E` `ray_on B A A` `ray_on B E N`] .
	have "ang_eq A B M A B N" using equalanglestransitive[OF `axioms` `ang_eq A B M A B E` `ang_eq A B E A B N`] .
	have "seg_eq B M B N" using `seg_eq B M B N` .
	have "seg_eq B A B A" using congruencereflexiveE[OF `axioms`] .
	have "seg_eq A M A N" using Prop04[OF `axioms` `seg_eq B A B A` `seg_eq B M B N` `ang_eq A B M A B N`] by blast
	have "ang_right B C D" using square_f[OF `axioms` `square A B C D`] by blast
	have "ang_right B C E" using square_f[OF `axioms` `square A B C E`] by blast
	have "ang_eq B C E B C D" using Euclid4[OF `axioms` `ang_right B C E` `ang_right B C D`] .
	have "seg_eq A B C D" using square_f[OF `axioms` `square A B C D`] by blast
	have "seg_eq A B C E" using square_f[OF `axioms` `square A B C E`] by blast
	have "seg_eq C E A B" using congruencesymmetric[OF `axioms` `seg_eq A B C E`] .
	have "seg_eq C E C D" using congruencetransitive[OF `axioms` `seg_eq C E A B` `seg_eq A B C D`] .
	have "\<not> col B C E" using rightangleNC[OF `axioms` `ang_right B C E`] .
	have "\<not> col B C D" using rightangleNC[OF `axioms` `ang_right B C D`] .
	have "seg_eq C B C B" using congruencereflexiveE[OF `axioms`] .
	have "seg_eq B E B D \<and> ang_eq C B E C B D \<and> ang_eq C E B C D B" using Prop04[OF `axioms` `seg_eq C B C B` `seg_eq C E C D` `ang_eq B C E B C D`] .
	have "ang_eq C B E C B D" using `seg_eq B E B D \<and> ang_eq C B E C B D \<and> ang_eq C E B C D B` by blast
	have "B \<noteq> C" using NCdistinct[OF `axioms` `\<not> col B C D`] by blast
	have "C = C" using equalityreflexiveE[OF `axioms`] .
	have "ray_on B C C" using ray4 `axioms` `C = C` `B \<noteq> C` by blast
	have "\<not> col B C D" using rightangleNC[OF `axioms` `ang_right B C D`] .
	have "\<not> col C B D" using NCorder[OF `axioms` `\<not> col B C D`] by blast
	have "ang_eq C B D C B D" using equalanglesreflexive[OF `axioms` `\<not> col C B D`] .
	have "ang_eq C B D C B M" using equalangleshelper[OF `axioms` `ang_eq C B D C B D` `ray_on B C C` `ray_on B D M`] .
	have "\<not> col C B E" using NCorder[OF `axioms` `\<not> col B C E`] by blast
	have "ang_eq C B E C B E" using equalanglesreflexive[OF `axioms` `\<not> col C B E`] .
	have "ray_on B E N" using `ray_on B E N` .
	have "ang_eq C B E C B N" using equalangleshelper[OF `axioms` `ang_eq C B E C B E` `ray_on B C C` `ray_on B E N`] .
	have "ang_eq C B E C B D" using equalanglestransitive[OF `axioms` `ang_eq C B E C B D` `ang_eq C B D C B D`] .
	have "ang_eq C B D C B E" using equalanglessymmetric[OF `axioms` `ang_eq C B E C B D`] .
	have "ang_eq C B M C B D" using equalanglessymmetric[OF `axioms` `ang_eq C B D C B M`] .
	have "ang_eq C B M C B E" using equalanglestransitive[OF `axioms` `ang_eq C B M C B D` `ang_eq C B D C B E`] .
	have "ang_eq C B M C B N" using equalanglestransitive[OF `axioms` `ang_eq C B M C B E` `ang_eq C B E C B N`] .
	have "ang_eq M B C N B C" using equalanglesflip[OF `axioms` `ang_eq C B M C B N`] .
	have "seg_eq B C B C" using congruencereflexiveE[OF `axioms`] .
	have "seg_eq M C N C" using Prop04[OF `axioms` `seg_eq B M B N` `seg_eq B C B C` `ang_eq M B C N B C`] by blast
	have "seg_eq A C A C" using congruencereflexiveE[OF `axioms`] .
	have "bet A N C" using betweennesspreserved[OF `axioms` `seg_eq A M A N` `seg_eq A C A C` `seg_eq M C N C` `bet A M C`] .
	have "A \<noteq> M" using betweennotequal[OF `axioms` `bet A M C`] by blast
	have "ray_on A M C" using ray4 `axioms` `bet A M C` `A \<noteq> M` by blast
	have "A \<noteq> N" using betweennotequal[OF `axioms` `bet A N C`] by blast
	have "ray_on A N C" using ray4 `axioms` `bet A N C` `A \<noteq> N` by blast
	have "ray_on A C N" using ray5[OF `axioms` `ray_on A N C`] .
	have "ray_on A C M" using ray5[OF `axioms` `ray_on A M C`] .
	have "M = N" using layoffunique[OF `axioms` `ray_on A C M` `ray_on A C N` `seg_eq A M A N`] .
	have "ray_on B N E" using ray5[OF `axioms` `ray_on B E N`] .
	have "ray_on B M D" using ray5[OF `axioms` `ray_on B D M`] .
	have "ray_on B M E" using `ray_on B N E` `M = N` by blast
	have "seg_eq B E B D" using `seg_eq B E B D \<and> ang_eq C B E C B D \<and> ang_eq C E B C D B` by blast
	have "E = D" using layoffunique[OF `axioms` `ray_on B M E` `ray_on B M D` `seg_eq B E B D`] .
	thus ?thesis by blast
qed

end