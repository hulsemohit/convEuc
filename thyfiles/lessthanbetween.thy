theory lessthanbetween
	imports Axioms Definitions Theorems
begin

theorem lessthanbetween:
	assumes: `axioms`
		"seg_lt A B A C"
		"ray_on A B C"
	shows: "bet A B C"
proof -
	obtain M where "bet A M C \<and> seg_eq A M A B" sorry
	have "bet A M C" using `bet A M C \<and> seg_eq A M A B` by blast
	have "seg_eq A M A B" using `bet A M C \<and> seg_eq A M A B` by blast
	have "A \<noteq> M" using betweennotequal[OF `axioms` `bet A M C`] by blast
	have "ray_on A M C" using ray4 `axioms` `bet A M C \<and> seg_eq A M A B` `A \<noteq> M` by blast
	have "ray_on A C M" using ray5[OF `axioms` `ray_on A M C`] .
	have "ray_on A C B" using ray5[OF `axioms` `ray_on A B C`] .
	have "M = B" using layoffunique[OF `axioms` `ray_on A C M` `ray_on A C B` `seg_eq A M A B`] .
	have "bet A B C" sorry
	thus ?thesis by blast
qed

end