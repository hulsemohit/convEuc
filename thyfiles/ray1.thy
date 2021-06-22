theory ray1
	imports Axioms Definitions Theorems
begin

theorem ray1:
	assumes: `axioms`
		"ray_on A B P"
	shows: "bet A P B \<or> B = P \<or> bet A B P"
proof -
	have "bet A P B \<or> B = P \<or> bet A B P"
	proof (rule ccontr)
		assume "\<not> (bet A P B \<or> B = P \<or> bet A B P)"
		have "\<not> (bet A P B) \<and> B \<noteq> P \<and> \<not> (bet A B P)" using `\<not> (bet A P B \<or> B = P \<or> bet A B P)` by blast
		have "\<not> (bet A P B)" using `\<not> (bet A P B) \<and> B \<noteq> P \<and> \<not> (bet A B P)` by blast
		have "B \<noteq> P" using `\<not> (bet A P B) \<and> B \<noteq> P \<and> \<not> (bet A B P)` by blast
		have "\<not> (bet A B P)" using `\<not> (bet A P B) \<and> B \<noteq> P \<and> \<not> (bet A B P)` by blast
		have "P \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> P`] .
		have "bet A B P" using ray[OF `axioms` `ray_on A B P` `P \<noteq> B` `\<not> (bet A P B)`] .
		show "False" using `bet A B P` `\<not> (bet A P B) \<and> B \<noteq> P \<and> \<not> (bet A B P)` by blast
	qed
	hence "bet A P B \<or> B = P \<or> bet A B P" by blast
	thus ?thesis by blast
qed

end