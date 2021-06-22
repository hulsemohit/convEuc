theory linereflectionisometry
	imports Axioms Definitions Theorems
begin

theorem linereflectionisometry:
	assumes: `axioms`
		"ang_right B A C"
		"ang_right A B D"
		"bet C A E"
		"bet D B F"
		"seg_eq A C A E"
		"seg_eq B D B F"
	shows: "seg_eq C D E F"
proof -
	obtain H where "bet B A H \<and> seg_eq B A H A \<and> seg_eq B C H C \<and> A \<noteq> C" sorry
	obtain G where "bet A B G \<and> seg_eq A B G B \<and> seg_eq A D G D \<and> B \<noteq> D" sorry
	have "bet A B G" using `bet A B G \<and> seg_eq A B G B \<and> seg_eq A D G D \<and> B \<noteq> D` by blast
	have "A \<noteq> B" using betweennotequal[OF `axioms` `bet A B G`] by blast
	obtain M where "bet A M B \<and> seg_eq M A M B" using Prop10[OF `axioms` `A \<noteq> B`]  by  blast
	have "bet A M B" using `bet A M B \<and> seg_eq M A M B` by blast
	have "seg_eq M A M B" using `bet A M B \<and> seg_eq M A M B` by blast
	have "ang_right D B A" using n8_2[OF `axioms` `ang_right A B D`] .
	have "B \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> B`] .
	have "bet B M A" using betweennesssymmetryE[OF `axioms` `bet A M B`] .
	have "ray_on B A M" using ray4 `axioms` `bet B M A` `B \<noteq> A` by blast
	have "ang_right D B M" using n8_3[OF `axioms` `ang_right D B A` `ray_on B A M`] .
	have "\<not> col D B M" using rightangleNC[OF `axioms` `ang_right D B M`] .
	have "\<not> (D = M)"
	proof (rule ccontr)
		assume "D = M"
		have "col D B M" using col_b `axioms` `D = M` by blast
		show "False" using `col D B M` `\<not> col D B M` by blast
	qed
	hence "D \<noteq> M" by blast
	have "M \<noteq> D" using inequalitysymmetric[OF `axioms` `D \<noteq> M`] .
	obtain R where "bet D M R \<and> seg_eq M R M D" using extensionE[OF `axioms` `D \<noteq> M` `M \<noteq> D`]  by  blast
	have "bet D M R" using `bet D M R \<and> seg_eq M R M D` by blast
	have "seg_eq M R M D" using `bet D M R \<and> seg_eq M R M D` by blast
	have "bet D B F" using `bet D B F` .
	have "seg_eq D B B F" using congruenceflip[OF `axioms` `seg_eq B D B F`] by blast
	have "col D B F" using col_b `axioms` `bet D B F` by blast
	have "B \<noteq> F" using betweennotequal[OF `axioms` `bet D B F`] by blast
	have "F \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> F`] .
	have "ang_right D B A" using n8_2[OF `axioms` `ang_right A B D`] .
	have "ang_right F B A" using collinearright[OF `axioms` `ang_right D B A` `col D B F` `F \<noteq> B`] .
	have "ang_right F B M" using n8_3[OF `axioms` `ang_right F B A` `ray_on B A M`] .
	have "\<not> col F B M" using rightangleNC[OF `axioms` `ang_right F B M`] .
	have "\<not> (F = M)"
	proof (rule ccontr)
		assume "F = M"
		have "col F B M" using col_b `axioms` `F = M` by blast
		show "False" using `col F B M` `\<not> col F B M` by blast
	qed
	hence "F \<noteq> M" by blast
	have "M \<noteq> F" using inequalitysymmetric[OF `axioms` `F \<noteq> M`] .
	obtain Q where "bet F M Q \<and> seg_eq M Q M F" using extensionE[OF `axioms` `F \<noteq> M` `M \<noteq> F`]  by  blast
	have "bet F M Q" using `bet F M Q \<and> seg_eq M Q M F` by blast
	have "seg_eq M Q M F" using `bet F M Q \<and> seg_eq M Q M F` by blast
	have "seg_eq M D M R" using congruencesymmetric[OF `axioms` `seg_eq M R M D`] .
	have "seg_eq D M M R" using congruenceflip[OF `axioms` `seg_eq M D M R`] by blast
	have "midpoint D M R" sorry
	have "seg_eq M F M Q" using congruencesymmetric[OF `axioms` `seg_eq M Q M F`] .
	have "seg_eq F M M Q" using congruenceflip[OF `axioms` `seg_eq M F M Q`] by blast
	have "midpoint F M Q" sorry
	have "seg_eq M B M A" using congruencesymmetric[OF `axioms` `seg_eq M A M B`] .
	have "seg_eq B M M A" using congruenceflip[OF `axioms` `seg_eq M B M A`] by blast
	have "bet B M A" using betweennesssymmetryE[OF `axioms` `bet A M B`] .
	have "midpoint B M A" sorry
	have "seg_eq F B Q A" using pointreflectionisometry[OF `axioms` `midpoint F M Q` `midpoint B M A`] .
	have "seg_eq B D B F" using `seg_eq B D B F` .
	have "seg_eq B F F B" using equalityreverseE[OF `axioms`] .
	have "seg_eq B D F B" using congruencetransitive[OF `axioms` `seg_eq B D B F` `seg_eq B F F B`] .
	have "ang_right B A C" using `ang_right B A C` .
	have "ang_right C A B" using n8_2[OF `axioms` `ang_right B A C`] .
	have "ray_on A B M" using ray4 `axioms` `bet A M B \<and> seg_eq M A M B` `A \<noteq> B` by blast
	have "ang_right C A M" using n8_3[OF `axioms` `ang_right C A B` `ray_on A B M`] .
	have "bet Q M F" using betweennesssymmetryE[OF `axioms` `bet F M Q`] .
	have "bet R M D" using betweennesssymmetryE[OF `axioms` `bet D M R`] .
	have "ang_right D B M" using `ang_right D B M` .
	have "bet D B F" using `bet D B F` .
	have "seg_eq D B B F" using congruenceflip[OF `axioms` `seg_eq B D B F`] by blast
	have "seg_eq D M F M" using rightreverse[OF `axioms` `ang_right D B M` `bet D B F` `seg_eq D B B F`] .
	have "seg_eq F M D M" using congruencesymmetric[OF `axioms` `seg_eq D M F M`] .
	have "seg_eq F M M Q" using congruenceflip[OF `axioms` `seg_eq M F M Q`] by blast
	have "seg_eq D M M R" using `seg_eq D M M R` .
	have "seg_eq Q M F M" using congruenceflip[OF `axioms` `seg_eq M Q M F`] by blast
	have "seg_eq Q M D M" using congruencetransitive[OF `axioms` `seg_eq Q M F M` `seg_eq F M D M`] .
	have "seg_eq Q M M R" using congruencetransitive[OF `axioms` `seg_eq Q M D M` `seg_eq D M M R`] .
	have "seg_eq Q M R M" using congruenceflip[OF `axioms` `seg_eq Q M M R`] by blast
	have "seg_eq M F M D" using congruenceflip[OF `axioms` `seg_eq F M D M`] by blast
	have "ang_right C A M" using `ang_right C A M` .
	have "bet C A E" using `bet C A E` .
	have "seg_eq C A A E" using congruenceflip[OF `axioms` `seg_eq A C A E`] by blast
	have "seg_eq C M E M" using rightreverse[OF `axioms` `ang_right C A M` `bet C A E` `seg_eq C A A E`] .
	have "seg_eq E M C M" using congruencesymmetric[OF `axioms` `seg_eq C M E M`] .
	have "seg_eq M E M C" using congruenceflip[OF `axioms` `seg_eq E M C M`] by blast
	have "midpoint D M R" sorry
	have "midpoint F M Q" sorry
	have "seg_eq M B M A" using congruencesymmetric[OF `axioms` `seg_eq M A M B`] .
	have "seg_eq B M M A" using congruenceflip[OF `axioms` `seg_eq M B M A`] by blast
	have "midpoint B M A" sorry
	have "seg_eq F B Q A" using pointreflectionisometry[OF `axioms` `midpoint F M Q` `midpoint B M A`] .
	have "seg_eq D B R A" using pointreflectionisometry[OF `axioms` `midpoint D M R` `midpoint B M A`] .
	have "seg_eq D B B F" using `seg_eq D B B F` .
	have "seg_eq Q A F B" using congruencesymmetric[OF `axioms` `seg_eq F B Q A`] .
	have "seg_eq B F D B" using congruencesymmetric[OF `axioms` `seg_eq D B B F`] .
	have "seg_eq F B D B" using congruenceflip[OF `axioms` `seg_eq B F D B`] by blast
	have "seg_eq Q A D B" using congruencetransitive[OF `axioms` `seg_eq Q A F B` `seg_eq F B D B`] .
	have "seg_eq Q A R A" using congruencetransitive[OF `axioms` `seg_eq Q A D B` `seg_eq D B R A`] .
	have "seg_eq Q A A R" using congruenceflip[OF `axioms` `seg_eq Q A R A`] by blast
	have "midpoint D M R" using `midpoint D M R` .
	have "midpoint F M Q" using `midpoint F M Q` .
	have "seg_eq D F R Q" using pointreflectionisometry[OF `axioms` `midpoint D M R` `midpoint F M Q`] .
	have "seg_eq F D Q R" using congruenceflip[OF `axioms` `seg_eq D F R Q`] by blast
	have "bet F B D" using betweennesssymmetryE[OF `axioms` `bet D B F`] .
	have "seg_eq F B Q A" using `seg_eq F B Q A` .
	have "seg_eq B D A R" using congruenceflip[OF `axioms` `seg_eq D B R A`] by blast
	have "bet Q A R" using betweennesspreserved[OF `axioms` `seg_eq F B Q A` `seg_eq F D Q R` `seg_eq B D A R` `bet F B D`] .
	have "midpoint Q A R" sorry
	have "seg_eq E A A C" using doublereverse[OF `axioms` `seg_eq C A A E`] by blast
	have "bet E A C" using betweennesssymmetryE[OF `axioms` `bet C A E`] .
	have "midpoint E A C" sorry
	have "seg_eq E Q C R" using pointreflectionisometry[OF `axioms` `midpoint E A C` `midpoint Q A R`] .
	have "seg_eq Q E R C" using congruenceflip[OF `axioms` `seg_eq E Q C R`] by blast
	have "seg_eq M E M C" using `seg_eq M E M C` .
	have "seg_eq Q M R M" using `seg_eq Q M R M` .
	have "seg_eq M F M D" using `seg_eq M F M D` .
	have "seg_eq E F C D" using 5-lineE[OF `axioms` `seg_eq M F M D` `seg_eq Q E R C` `seg_eq M E M C` `bet Q M F` `bet R M D` `seg_eq Q M R M`] .
	have "seg_eq C D E F" using congruencesymmetric[OF `axioms` `seg_eq E F C D`] .
	thus ?thesis by blast
qed

end