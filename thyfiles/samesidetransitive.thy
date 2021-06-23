theory samesidetransitive
	imports Geometry planeseparation
begin

theorem samesidetransitive:
	assumes "axioms"
		"same_side P Q A B"
		"same_side Q R A B"
	shows "same_side P R A B"
proof -
	obtain E F G where "col A B E \<and> col A B F \<and> bet Q E G \<and> bet R F G \<and> \<not> col A B Q \<and> \<not> col A B R" using sameside_f[OF `axioms` `same_side Q R A B`]  by  blast
	have "col A B E" using `col A B E \<and> col A B F \<and> bet Q E G \<and> bet R F G \<and> \<not> col A B Q \<and> \<not> col A B R` by blast
	have "col A B F" using `col A B E \<and> col A B F \<and> bet Q E G \<and> bet R F G \<and> \<not> col A B Q \<and> \<not> col A B R` by blast
	have "bet Q E G" using `col A B E \<and> col A B F \<and> bet Q E G \<and> bet R F G \<and> \<not> col A B Q \<and> \<not> col A B R` by blast
	have "bet R F G" using `col A B E \<and> col A B F \<and> bet Q E G \<and> bet R F G \<and> \<not> col A B Q \<and> \<not> col A B R` by blast
	have "\<not> col A B Q" using `col A B E \<and> col A B F \<and> bet Q E G \<and> bet R F G \<and> \<not> col A B Q \<and> \<not> col A B R` by blast
	have "\<not> col A B R" using `col A B E \<and> col A B F \<and> bet Q E G \<and> bet R F G \<and> \<not> col A B Q \<and> \<not> col A B R` by blast
	have "oppo_side Q A B G" using oppositeside_b[OF `axioms` `bet Q E G` `col A B E` `\<not> col A B Q`] .
	have "oppo_side P A B G" using planeseparation[OF `axioms` `same_side P Q A B` `oppo_side Q A B G`] .
	obtain M where "bet P M G \<and> col A B M \<and> \<not> col A B P" using oppositeside_f[OF `axioms` `oppo_side P A B G`]  by  blast
	have "bet P M G" using `bet P M G \<and> col A B M \<and> \<not> col A B P` by blast
	have "col A B M" using `bet P M G \<and> col A B M \<and> \<not> col A B P` by blast
	have "\<not> col A B P" using `bet P M G \<and> col A B M \<and> \<not> col A B P` by blast
	have "same_side P R A B" using sameside_b[OF `axioms` `col A B M` `col A B F` `bet P M G` `bet R F G` `\<not> col A B P` `\<not> col A B R`] .
	thus ?thesis by blast
qed

end