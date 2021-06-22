theory samesidetransitive
	imports Axioms Definitions Theorems
begin

theorem samesidetransitive:
	assumes: `axioms`
		"same_side P Q A B"
		"same_side Q R A B"
	shows: "same_side P R A B"
proof -
	obtain E F G where "col A B E \<and> col A B F \<and> bet Q E G \<and> bet R F G \<and> \<not> col A B Q \<and> \<not> col A B R" sorry
	have "col A B E" using `col A B E \<and> col A B F \<and> bet Q E G \<and> bet R F G \<and> \<not> col A B Q \<and> \<not> col A B R` by blast
	have "col A B F" using `col A B E \<and> col A B F \<and> bet Q E G \<and> bet R F G \<and> \<not> col A B Q \<and> \<not> col A B R` by blast
	have "bet Q E G" using `col A B E \<and> col A B F \<and> bet Q E G \<and> bet R F G \<and> \<not> col A B Q \<and> \<not> col A B R` by blast
	have "bet R F G" using `col A B E \<and> col A B F \<and> bet Q E G \<and> bet R F G \<and> \<not> col A B Q \<and> \<not> col A B R` by blast
	have "\<not> col A B Q" using `col A B E \<and> col A B F \<and> bet Q E G \<and> bet R F G \<and> \<not> col A B Q \<and> \<not> col A B R` by blast
	have "\<not> col A B R" using `col A B E \<and> col A B F \<and> bet Q E G \<and> bet R F G \<and> \<not> col A B Q \<and> \<not> col A B R` by blast
	have "oppo_side Q A B G" sorry
	have "oppo_side P A B G" using planeseparation[OF `axioms` `same_side P Q A B` `oppo_side Q A B G`] .
	obtain M where "bet P M G \<and> col A B M \<and> \<not> col A B P" sorry
	have "bet P M G" using `bet P M G \<and> col A B M \<and> \<not> col A B P` by blast
	have "col A B M" using `bet P M G \<and> col A B M \<and> \<not> col A B P` by blast
	have "\<not> col A B P" using `bet P M G \<and> col A B M \<and> \<not> col A B P` by blast
	have "same_side P R A B" sorry
	thus ?thesis by blast
qed

end