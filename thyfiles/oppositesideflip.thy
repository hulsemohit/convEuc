theory oppositesideflip
	imports Axioms Definitions Theorems
begin

theorem oppositesideflip:
	assumes: `axioms`
		"oppo_side P A B Q"
	shows: "oppo_side P B A Q"
proof -
	obtain r where "bet P r Q \<and> col A B r \<and> \<not> col A B P" sorry
	have "bet P r Q" using `bet P r Q \<and> col A B r \<and> \<not> col A B P` by blast
	have "col A B r" using `bet P r Q \<and> col A B r \<and> \<not> col A B P` by blast
	have "\<not> col A B P" using `bet P r Q \<and> col A B r \<and> \<not> col A B P` by blast
	have "\<not> col B A P" using NCorder[OF `axioms` `\<not> col A B P`] by blast
	have "col B A r" using collinearorder[OF `axioms` `col A B r`] by blast
	have "oppo_side P B A Q" sorry
	thus ?thesis by blast
qed

end