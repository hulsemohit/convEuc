theory ray2
	imports Geometry betweennotequal
begin

theorem ray2:
	assumes "axioms"
		"ray_on A B C"
	shows "A \<noteq> B"
proof -
	obtain E where "bet E A C \<and> bet E A B" using ray_f[OF `axioms` `ray_on A B C`]  by  blast
	have "bet E A B" using `bet E A C \<and> bet E A B` by blast
	have "A \<noteq> B" using betweennotequal[OF `axioms` `bet E A B`] by blast
	thus ?thesis by blast
qed

end