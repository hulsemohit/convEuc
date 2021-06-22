theory rightreverse
	imports Axioms Definitions Theorems
begin

theorem rightreverse:
	assumes: `axioms`
		"ang_right A B C"
		"bet A B D"
		"seg_eq A B B D"
	shows: "seg_eq A C D C"
proof -
	obtain E where "bet A B E \<and> seg_eq A B E B \<and> seg_eq A C E C \<and> B \<noteq> C" sorry
	have "bet A B E" using `bet A B E \<and> seg_eq A B E B \<and> seg_eq A C E C \<and> B \<noteq> C` by blast
	have "seg_eq A B E B" using `bet A B E \<and> seg_eq A B E B \<and> seg_eq A C E C \<and> B \<noteq> C` by blast
	have "seg_eq A C E C" using `bet A B E \<and> seg_eq A B E B \<and> seg_eq A C E C \<and> B \<noteq> C` by blast
	have "seg_eq B D A B" using congruencesymmetric[OF `axioms` `seg_eq A B B D`] .
	have "seg_eq B D E B" using congruencetransitive[OF `axioms` `seg_eq B D A B` `seg_eq A B E B`] .
	have "seg_eq B D B E" using congruenceflip[OF `axioms` `seg_eq B D E B`] by blast
	have "D = E" using extensionunique[OF `axioms` `bet A B D` `bet A B E` `seg_eq B D B E`] .
	have "seg_eq A C D C" sorry
	thus ?thesis by blast
qed

end