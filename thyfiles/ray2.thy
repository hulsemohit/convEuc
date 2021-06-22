theory ray2
	imports Axioms Definitions Theorems
begin

theorem ray2:
	assumes: `axioms`
		"ray_on A B C"
	shows: "A \<noteq> B"
proof -
	obtain E where "bet E A C \<and> bet E A B" sorry
	have "bet E A B" using `bet E A C \<and> bet E A B` by blast
	have "A \<noteq> B" using betweennotequal[OF `axioms` `bet E A B`] by blast
	thus ?thesis by blast
qed

end