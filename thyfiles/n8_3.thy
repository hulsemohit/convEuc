theory n8_3
	imports Axioms Definitions Theorems
begin

theorem n8_3:
	assumes: `axioms`
		"ang_right A B C"
		"ray_on B C D"
	shows: "ang_right A B D"
proof -
	obtain E where "bet A B E \<and> seg_eq A B E B \<and> seg_eq A C E C \<and> B \<noteq> C" sorry
	have "bet A B E" using `bet A B E \<and> seg_eq A B E B \<and> seg_eq A C E C \<and> B \<noteq> C` by blast
	have "seg_eq A B E B" using `bet A B E \<and> seg_eq A B E B \<and> seg_eq A C E C \<and> B \<noteq> C` by blast
	have "seg_eq A C E C" using `bet A B E \<and> seg_eq A B E B \<and> seg_eq A C E C \<and> B \<noteq> C` by blast
	have "seg_eq B C B C" using congruencereflexiveE[OF `axioms`] .
	have "seg_eq C D C D" using congruencereflexiveE[OF `axioms`] .
	have "seg_eq B A B E" using congruenceflip[OF `axioms` `seg_eq A B E B`] by blast
	have "seg_eq C A C E" using congruenceflip[OF `axioms` `seg_eq A C E C`] by blast
	have "bet B D C \<or> C = D \<or> bet B C D" using ray1[OF `axioms` `ray_on B C D`] .
	consider "bet B D C"|"C = D"|"bet B C D" using `bet B D C \<or> C = D \<or> bet B C D`  by blast
	hence ang_right A B D
	proof (cases)
		case 1
		have "seg_eq B D B D" using congruencereflexiveE[OF `axioms`] .
		have "seg_eq D C D C" using congruencereflexiveE[OF `axioms`] .
		have "seg_eq B A B E" using `seg_eq B A B E` .
		have "seg_eq C A C E" using `seg_eq C A C E` .
		have "seg_eq D A D E" using interior5[OF `axioms` `bet B D C` `bet B D C` `seg_eq B D B D` `seg_eq D C D C` `seg_eq B A B E` `seg_eq C A C E`] .
		have "seg_eq A D E D" using congruenceflip[OF `axioms` `seg_eq D A D E`] by blast
		have "B \<noteq> D" using betweennotequal[OF `axioms` `bet B D C`] by blast
		have "bet A B E \<and> seg_eq A B E B \<and> seg_eq A D E D \<and> B \<noteq> D" using `bet A B E \<and> seg_eq A B E B \<and> seg_eq A C E C \<and> B \<noteq> C` `bet A B E \<and> seg_eq A B E B \<and> seg_eq A C E C \<and> B \<noteq> C` `seg_eq A D E D` `B \<noteq> D` by blast
		have "ang_right A B D" sorry
	next
		case 2
		have "ang_right A B D" sorry
	next
		case 3
		have "seg_eq A D E D" using 5-lineE[OF `axioms` `seg_eq C D C D` `seg_eq B A B E` `seg_eq C A C E` `bet B C D` `bet B C D` `seg_eq B C B C`] .
		have "B \<noteq> D" using betweennotequal[OF `axioms` `bet B C D`] by blast
		have "bet A B E \<and> seg_eq A B E B \<and> seg_eq A D E D \<and> B \<noteq> D" using `bet A B E \<and> seg_eq A B E B \<and> seg_eq A C E C \<and> B \<noteq> C` `bet A B E \<and> seg_eq A B E B \<and> seg_eq A C E C \<and> B \<noteq> C` `seg_eq A D E D` `B \<noteq> D` by blast
		have "ang_right A B D" sorry
	next
	thus ?thesis by blast
qed

end