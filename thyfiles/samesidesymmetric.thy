theory samesidesymmetric
	imports Axioms Definitions Theorems
begin

theorem samesidesymmetric:
	assumes: `axioms`
		"same_side P Q A B"
	shows: "same_side Q P A B \<and> same_side P Q B A \<and> same_side Q P B A"
proof -
	obtain E F G where "col A B E \<and> col A B F \<and> bet P E G \<and> bet Q F G \<and> \<not> col A B P \<and> \<not> col A B Q" sorry
	have "col A B E" using `col A B E \<and> col A B F \<and> bet P E G \<and> bet Q F G \<and> \<not> col A B P \<and> \<not> col A B Q` by blast
	have "col A B F" using `col A B E \<and> col A B F \<and> bet P E G \<and> bet Q F G \<and> \<not> col A B P \<and> \<not> col A B Q` by blast
	have "bet P E G" using `col A B E \<and> col A B F \<and> bet P E G \<and> bet Q F G \<and> \<not> col A B P \<and> \<not> col A B Q` by blast
	have "bet Q F G" using `col A B E \<and> col A B F \<and> bet P E G \<and> bet Q F G \<and> \<not> col A B P \<and> \<not> col A B Q` by blast
	have "\<not> col A B P" using `col A B E \<and> col A B F \<and> bet P E G \<and> bet Q F G \<and> \<not> col A B P \<and> \<not> col A B Q` by blast
	have "\<not> col A B Q" using `col A B E \<and> col A B F \<and> bet P E G \<and> bet Q F G \<and> \<not> col A B P \<and> \<not> col A B Q` by blast
	have "same_side Q P A B" sorry
	have "col B A E" using collinearorder[OF `axioms` `col A B E`] by blast
	have "col B A F" using collinearorder[OF `axioms` `col A B F`] by blast
	have "\<not> col B A P" using NCorder[OF `axioms` `\<not> col A B P`] by blast
	have "\<not> col B A Q" using NCorder[OF `axioms` `\<not> col A B Q`] by blast
	have "same_side P Q B A" sorry
	have "same_side Q P B A" sorry
	have "same_side Q P A B \<and> same_side P Q B A \<and> same_side Q P B A" using `same_side Q P A B` `same_side P Q B A` `same_side Q P B A` by blast
	thus ?thesis by blast
qed

end